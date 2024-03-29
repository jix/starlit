use clap::{ArgEnum, Parser};
use flussab::DeferredWriter;
use mimalloc::MiMalloc;
use starlit::{
    lit::Lit,
    log::{info, LogLevel},
    proof::drat::{BinaryDrat, Drat},
};

#[global_allocator]
static GLOBAL: MiMalloc = MiMalloc;

#[derive(Parser)]
struct Args {
    /// Input formula in DIMACS CNF format.
    input_file: std::path::PathBuf,

    /// Optional proof output in DRAT format.
    ///
    /// Will not overwrite an existing file.
    proof_file: Option<std::path::PathBuf>,

    /// Proof format to generate.
    #[clap(long, arg_enum, default_value = "binary-drat")]
    proof_format: ProofFormat,

    /// Make output more verbose (use multiple times for more verbose output).
    #[clap(long, short = 'v', parse(from_occurrences))]
    verbose: u8,

    /// Make output less verbose.
    #[clap(long, short = 'q', parse(from_occurrences), conflicts_with = "verbose")]
    quiet: u8,

    /// Include originating source locations in log messages.
    #[clap(long)]
    log_src: bool,
}

#[derive(Copy, Clone, ArgEnum, Debug)]
enum ProofFormat {
    Drat,
    BinaryDrat,
}

fn main() -> anyhow::Result<()> {
    let args = Args::parse();

    let mut solver = starlit::solver::Solver::default();

    match (args.verbose, args.quiet) {
        (0, 0) => solver.ctx.logger.set_log_level(Some(LogLevel::Info)),
        (1, _) => solver.ctx.logger.set_log_level(Some(LogLevel::Verbose)),
        (2, _) => solver.ctx.logger.set_log_level(Some(LogLevel::Debug)),
        (_, 0) => solver.ctx.logger.set_log_level(Some(LogLevel::Trace)),
        _ => solver.ctx.logger.set_log_level(None),
    }

    solver.ctx.logger.log_source_locations(args.log_src);

    info!(solver, "Starlit SAT Solver");

    if let Some(proof_file) = args.proof_file {
        let proof_writer = DeferredWriter::from_write(
            std::fs::File::options()
                .write(true)
                .create_new(true)
                .open(proof_file)?,
        );

        solver.write_proof(match args.proof_format {
            ProofFormat::Drat => Box::new(Drat::new(proof_writer)),
            ProofFormat::BinaryDrat => Box::new(BinaryDrat::new(proof_writer)),
        });
    }

    let mut input = flussab_cnf::cnf::Parser::from_read(
        std::fs::File::open(&args.input_file)?,
        flussab_cnf::cnf::Config::default(),
    )?;

    let header = input
        .header()
        .ok_or_else(|| anyhow::anyhow!("no header in input file"))?;

    while let Some(clause) = input.next_clause()? {
        solver.add_clause(clause);
    }

    let satisfiable = solver.solve();

    let duration = solver.ctx.logger.time();

    let duration_secs = duration.as_secs_f64();

    info!(solver, = satisfiable, = duration);
    info!(
        solver,
        conflicts = solver.ctx.stats.search.conflicts,
        per_sec = (solver.ctx.stats.search.conflicts as f64 / duration_secs),
    );
    info!(
        solver,
        decisions = solver.ctx.stats.search.decisions,
        per_conflict =
            solver.ctx.stats.search.decisions as f64 / solver.ctx.stats.search.conflicts as f64,
    );
    info!(
        solver,
        propagations = solver.ctx.stats.prop.propagations,
        per_sec = solver.ctx.stats.prop.propagations as f64 / duration_secs,
    );

    solver.close_proof()?;

    if satisfiable {
        println!("s SATISFIABLE");
        let mut line = String::default();

        for lit in (0..header.var_count).map(|index| Lit::from_index(index, true)) {
            if let Some(value) = solver.value(lit) {
                use std::fmt::Write;

                let len = line.len();

                write!(&mut line, " {}", lit ^ !value).unwrap();

                if line.len() > 77 {
                    line.truncate(len);
                    println!("v{}", line);
                    line.clear();
                    write!(&mut line, " {}", lit ^ !value).unwrap();
                }
            }
        }
        if !line.is_empty() {
            println!("v{}", line);
        }
        println!("v 0");
        std::process::exit(20);
    } else {
        println!("s UNSATISFIABLE");
        std::process::exit(20);
    }
}

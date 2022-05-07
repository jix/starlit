use clap::Parser;
use mimalloc::MiMalloc;
use starlit::{
    lit::Lit,
    log::{info, LogLevel},
};

#[global_allocator]
static GLOBAL: MiMalloc = MiMalloc;

#[derive(Parser)]
struct Args {
    /// Input formula in DIMACS CNF format.
    input_file: std::path::PathBuf,

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

fn main() -> anyhow::Result<()> {
    let args = Args::parse();

    let start = std::time::Instant::now();

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

    let end = std::time::Instant::now();
    let duration = end - start;

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

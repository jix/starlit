use std::io::Write;

use mimalloc::MiMalloc;
use starlit::{
    clauses::long::SolverClauseData,
    lit::{Lit, Var},
    tracking::TracksVarCount,
    trail::{DecisionLevel, Reason, Step},
};
use tracing_subscriber::fmt::MakeWriter;

#[global_allocator]
static GLOBAL: MiMalloc = MiMalloc;

struct CommentWriter;

impl<'a> MakeWriter<'a> for CommentWriter {
    type Writer = std::io::Stdout;

    fn make_writer(&self) -> Self::Writer {
        let mut writer = std::io::stdout();
        writer.write_all(b"c ").unwrap();
        writer
    }
}

fn main() -> anyhow::Result<()> {
    tracing_subscriber::fmt()
        .with_timer(tracing_subscriber::fmt::time::uptime())
        .with_level(true)
        .with_target(true)
        .with_env_filter(tracing_subscriber::EnvFilter::new(
            std::env::var("STARLIT_LOG").as_deref().unwrap_or("info"),
        ))
        .with_writer(CommentWriter)
        .init();

    tracing::info!("Starlit SAT Solver");

    let start = std::time::Instant::now();

    // Just a temporary hack to easily allow manual testing from the command line.
    let mut solver = starlit::solver::Solver::default();

    let mut input = flussab_cnf::cnf::Parser::from_read(
        std::fs::File::open(
            std::env::args_os()
                .nth(1)
                .ok_or_else(|| anyhow::anyhow!("no input formula"))?,
        )?,
        flussab_cnf::cnf::Config::default(),
    )?;

    let header = input
        .header()
        .ok_or_else(|| anyhow::anyhow!("no header in input file"))?;

    solver.set_var_count(header.var_count);

    let mut units = vec![];

    while let Some(clause) = input.next_clause()? {
        if let [unit] = *clause {
            units.push(unit);
        } else {
            solver
                .search
                .clauses
                .add_clause(SolverClauseData::new_input_clause(), clause);
        }
    }

    for unit in units {
        if solver.search.trail.assigned.is_false(unit) {
            tracing::info!("unit conflict");
            println!("s UNSATISFIABLE");
            std::process::exit(20);
        } else if solver.search.trail.assigned.is_true(unit) {
            continue;
        }
        solver.search.trail.assign(Step {
            assigned_lit: unit,
            decision_level: DecisionLevel::TOP,
            reason: Reason::Unit,
        });
    }

    let satisfiable = solver.solve();

    let end = std::time::Instant::now();
    let duration = end - start;

    let duration_secs = duration.as_secs_f64();

    tracing::info!(satisfiable, ?duration);
    tracing::info!(
        conflicts = solver.search.stats.conflicts,
        per_sec = ?solver.search.stats.conflicts as f64 / duration_secs,
    );
    tracing::info!(
        decisions = solver.search.stats.decisions,
        per_conflict = ?solver.search.stats.decisions as f64 / solver.search.stats.conflicts as f64,
    );
    tracing::info!(
        propagations = solver.search.stats.propagations,
        per_sec = ?solver.search.stats.propagations as f64 / duration_secs,
    );

    if satisfiable {
        println!("s SATISFIABLE");
        print!("v ");
        for var in (0..header.var_count).map(Var::from_index) {
            let lit = Lit::from_var(var, true);
            let negate = solver.search.trail.assigned.is_false(lit);
            print!("{} ", lit ^ negate);
        }
        println!("0");
        std::process::exit(20);
    } else {
        println!("s UNSATISFIABLE");
        std::process::exit(20);
    }
}

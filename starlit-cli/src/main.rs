use starlit::{
    tracking::TracksVarCount,
    trail::{Reason, Step},
};

fn main() -> anyhow::Result<()> {
    tracing_subscriber::fmt()
        .with_timer(tracing_subscriber::fmt::time::uptime())
        .with_level(true)
        .with_target(true)
        .with_env_filter(tracing_subscriber::EnvFilter::new(
            std::env::var("STARLIT_LOG").as_deref().unwrap_or(&"info"),
        ))
        .init();

    tracing::info!("Starlit SAT Solver");

    let start = std::time::Instant::now();

    // Just a temporary hack to easily allow manual testing from the command line.
    let mut search = starlit::search::Search::default();

    let mut input = flussab_cnf::cnf::Parser::from_read(
        std::fs::File::open(
            std::env::args_os()
                .nth(1)
                .ok_or_else(|| anyhow::anyhow!("no input formula"))?,
        )?,
        true,
    )?;

    let header = input
        .header()
        .ok_or_else(|| anyhow::anyhow!("no header in input file"))?;

    search.set_var_count(header.var_count);

    let mut units = vec![];

    while let Some(clause) = input.next_clause()? {
        if let [unit] = *clause {
            units.push(unit);
        } else {
            search.clauses.add_clause(&clause);
        }
    }

    for unit in units {
        if search.trail.assigned.is_false(unit) {
            println!("{:?}", false);
            return Ok(());
        } else if search.trail.assigned.is_true(unit) {
            continue;
        }
        search.trail.assign(Step {
            assigned_lit: unit,
            decision_level: 0,
            reason: Reason::Unit,
        });
    }

    let satisfiable = search.search();

    let end = std::time::Instant::now();
    let duration = end - start;

    let duration_secs = duration.as_secs_f64();

    tracing::info!(satisfiable, ?duration);
    tracing::info!(
        conflicts = search.stats.conflicts,
        per_sec = ?search.stats.conflicts as f64 / duration_secs,
    );
    tracing::info!(
        decisions = search.stats.decisions,
        per_conflict = ?search.stats.decisions as f64 / search.stats.conflicts as f64,
    );
    tracing::info!(
        propagations = search.stats.propagations,
        per_sec = ?search.stats.propagations as f64 / duration_secs,
    );

    Ok(())
}

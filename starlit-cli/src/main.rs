use starlit::{
    tracking::TracksVarCount,
    trail::{Reason, Step},
};

fn main() -> anyhow::Result<()> {
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

    println!("{:?}", search.search());

    Ok(())
}

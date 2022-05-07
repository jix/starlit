//! Progress reports.

use crate::{context::Ctx, log::LogLevel};

/// Logs a progress report containing various useful statistics.
#[track_caller]
pub fn report(ctx: &mut Ctx) {
    let stats = &ctx.stats;
    ctx.logger.log(LogLevel::Info, |msg| {
        msg.add_message("red:");
        msg.add_value(&format_args!("{:2}", stats.search.reductions));
        msg.add_message("res:");
        msg.add_value(&format_args!("{:3}", stats.search.restarts));
        msg.add_message("cfl:");
        msg.add_value(&format_args!("{:5}", stats.search.conflicts));
        msg.add_message("bin:");
        msg.add_value(&format_args!("{:2}", stats.formula.binary));
        msg.add_message("red:");
        msg.add_value(&format_args!("{:3}", stats.formula.redundant));
        msg.add_message("irr:");
        msg.add_value(&format_args!("{:3}", stats.formula.irredundant));
        msg.add_message("var:");

        let vars_left = stats.formula.vars - stats.prop.fixed_vars;
        msg.add_value(&format_args!(
            "{:3}",
            stats.formula.vars - stats.prop.fixed_vars
        ));
        msg.add_value(&format_args!(
            "{}%",
            vars_left * 100 / (stats.formula.vars).max(1)
        ));
    })
}

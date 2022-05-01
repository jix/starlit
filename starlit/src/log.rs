//! Solver internal logging.
use std::{fmt::Debug, io::Write, panic::Location};

/// Log levels used for solver internal logging.
///
/// The levels are listed from less to more verbose.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum LogLevel {
    /// Default log level
    Info,
    /// More logging
    Verbose,
    /// Detailed logging
    Debug,
    /// Log everything
    Trace,
}

pub use starlit_macros::{debug, info, trace, verbose};

/// Solver internal logger.
#[derive(Default)]
pub struct Logger {
    level_limit: u8,
    log_source_locations: bool,
}

impl Logger {
    /// Limits generated log messages to at most the given log level.
    pub fn set_log_level(&mut self, level: Option<LogLevel>) {
        if let Some(level) = level {
            self.level_limit = level as u8 + 1;
        } else {
            self.level_limit = 0;
        }
    }

    /// Sets whether to print source locations for log messages.
    pub fn log_source_locations(&mut self, log_source_locations: bool) {
        self.log_source_locations = log_source_locations
    }

    /// Logs a message.
    ///
    /// The log message is populated by the `action` closure passed. The closure will only be called
    /// if the given `level` is currently active.
    #[inline(always)]
    #[track_caller]
    pub fn log(&self, level: LogLevel, action: impl for<'a> FnOnce(&'a mut dyn LogMessage)) {
        if (level as u8) < self.level_limit {
            self.perform_log(level, Location::caller(), action)
        }
    }

    #[inline(never)]
    #[cold]
    fn perform_log(
        &self,
        level: LogLevel,
        location: &'static Location<'static>,
        action: impl for<'a> FnOnce(&'a mut dyn LogMessage),
    ) {
        let out = std::io::stdout();
        let mut out = out.lock();

        let prefix = match level {
            LogLevel::Info => "c",
            LogLevel::Verbose => "c V:",
            LogLevel::Debug => "c D:",
            LogLevel::Trace => "c T:",
        };
        write!(out, "{prefix}").unwrap();
        action(&mut out);
        let file = location.file();
        let line = location.line();
        if self.log_source_locations {
            writeln!(out, " \x1b[34m{file}:{line}\x1b[0m").unwrap();
        } else {
            writeln!(out).unwrap();
        }
    }
}

/// Construct a log message.
pub trait LogMessage {
    /// Adds a (space separated) static string to the message.
    fn add_message(&mut self, message: &'static str);

    /// Adds a (space separated) value to the message.
    fn add_value(&mut self, value: &dyn Debug);
}

impl<T> LogMessage for T
where
    T: std::io::Write,
{
    fn add_message(&mut self, message: &'static str) {
        write!(self, " {message}").unwrap();
    }

    fn add_value(&mut self, value: &dyn Debug) {
        write!(self, " {value:?}").unwrap();
    }
}

/// Retreives the logger from some context.
pub trait HasLogger {
    /// Retreives the logger from some context.
    fn logger(&self) -> &Logger;
}

impl HasLogger for Logger {
    #[inline(always)]
    fn logger(&self) -> &Logger {
        self
    }
}

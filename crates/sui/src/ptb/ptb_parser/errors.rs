// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

use std::collections::BTreeMap;

use miette::{miette, LabeledSpan};
use thiserror::Error;

use crate::ptb::ptb::PTBCommand;

use super::{argument::Span, context::FileScope};

pub type PTBResult<T> = Result<T, PTBError>;

/// An error that occurred while working with a PTB. This error contains an error message along
/// with the file scope (file name and command index) where the error occurred.
#[derive(Debug, Clone, Error)]
pub enum PTBError {
    #[error("{message} at command {} in file '{}' {:?}", file_scope.file_command_index, file_scope.name, span)]
    WithSource {
        file_scope: FileScope,
        message: String,
        span: Option<Span>,
    },
}

#[macro_export]
macro_rules! error {
    ($x:expr, $($arg:tt)*) => {
        return Err($crate::err!($x, $($arg)*))
    };
    (sp: $l:expr, $x:expr, $($arg:tt)*) => {
        return Err($crate::err!(sp: $l, $x, $($arg)*))
    };
}

#[macro_export]
macro_rules! err {
    ($x:expr, $($arg:tt)*) => {
        $crate::ptb::ptb_parser::errors::PTBError::WithSource {
            file_scope: $x.context.current_file_scope().clone(),
            message: format!($($arg)*),
            span: None,
        }
    };
    (sp: $l:expr, $x:expr, $($arg:tt)*) => {
        $crate::ptb::ptb_parser::errors::PTBError::WithSource {
            file_scope: $x.context.current_file_scope().clone(),
            message: format!($($arg)*),
            span: Some($l),
        }
    };
}

// If no span we point to the command name
// If span, we convert the span range to the appropriate offset in the whole string
fn convert_span(original_command: PTBCommand, error: PTBError) -> (String, LabeledSpan, String) {
    let PTBError::WithSource {
        span,
        file_scope,
        message,
    } = error;
    let (range, command_string) = match span {
        None => (
            0..original_command.name.len(),
            original_command.name + " " + &original_command.values.join(" "),
        ),
        Some(span) => {
            println!("span: {:?}", span);
            let mut offset = original_command.name.len();
            let mut final_string = original_command.name.clone();
            let mut range = (span.start, span.end);
            for (i, arg) in original_command.values.iter().enumerate() {
                offset += 1;
                final_string.push_str(" ");
                if i != span.arg_idx {
                    offset += arg.len();
                    final_string.push_str(arg);
                } else {
                    range.0 += offset;
                    range.1 += offset;
                    offset += arg.len();
                    final_string.push_str(arg);
                }
            }
            (range.0..range.1, final_string)
        }
    };
    println!("Range after: {:?}", range);
    let label = LabeledSpan::at(range, message.clone());
    let error_string = format!(
        "{} {}",
        file_scope.file_command_index,
        if file_scope.name == "console" {
            "from console input".to_string()
        } else {
            format!("in PTB file '{}'", file_scope.name)
        }
    );

    (command_string, label, error_string)
}

pub fn convert_to_displayable_error(
    original_command: PTBCommand,
    error: PTBError,
) -> miette::Report {
    let (command_string, label, formatted_error) = convert_span(original_command, error);
    miette!(labels = vec![label], "Error at command {}", formatted_error)
        .with_source_code(command_string)
}

pub fn render_errors(
    commands: BTreeMap<usize, PTBCommand>,
    errors: Vec<PTBError>,
) -> Vec<miette::Report> {
    let mut rendered = vec![];
    // TODO: Handle file/local scopes here.
    for error in errors {
        let command_idx = match &error {
            PTBError::WithSource { file_scope, .. } => file_scope.file_command_index + 1,
        };
        let command = commands.get(&command_idx).unwrap();
        rendered.push(convert_to_displayable_error(command.clone(), error));
    }
    rendered
}

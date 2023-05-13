use crate::ast::{Node, Stmt};
use crate::Result;
use crate::{parser};
use std::fs::File;
use std::io::{BufReader};

/// A State is an opaque structure representing per thread Lua state.
#[derive(Debug)]
pub struct State {}

impl State {
    /// Creates a new thread running in a new, independent state.
    ///
    /// # Example
    ///
    /// ```
    /// use lua::state::State;
    ///
    /// let state = State::new();
    /// ```
    pub fn new() -> State {
        State {}
    }

    pub fn parse_file(&mut self, path: &str) -> Result<Vec<Node<Stmt>>> {
        let f = File::open(path)?;
        let reader = BufReader::new(f);

        let mut parser = parser::Parser::new(reader, path.to_string());
        parser.parse()
    }
}

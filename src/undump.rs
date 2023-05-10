use crate::Result;
use std::io::{BufReader, Read};

pub fn undump<T: Read>(_reader: BufReader<T>) -> Result<()> {
    unimplemented!()
}

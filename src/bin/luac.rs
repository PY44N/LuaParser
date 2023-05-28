extern crate lua_parser;

use lua_parser::state::State;

fn main() {
    let mut state = State::new();
    let result = state.parse_file("test.lua");
    match result {
        Ok((ast, vars)) => {
            println!("{:?}", ast);
            println!("{:?}", vars);
        }
        Err(e) => println!("Error=>{:?}", e),
    };
}

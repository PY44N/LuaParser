extern crate lua_parser;

use lua_parser::state::State;

fn main() {
    let mut state = State::new();
    let result = state.parse_file("test.lua");
    match result {
        Ok(res) => {
            println!("{:?}", res.ast);
            println!("{:?}", res.locals);
        }
        Err(e) => println!("Error=>{:?}", e),
    };
}

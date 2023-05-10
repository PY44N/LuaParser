extern crate lua;

use lua::state::State;

fn main() {
    let mut state = State::new();
    let result = state.parse_file("test.lua");
    match result {
        Ok(ast) => {
            println!("{:?}", ast);
        }
        Err(e) => println!("Error=>{:?}", e),
    };
}

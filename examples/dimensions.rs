extern crate simon;

use simon::*;

#[derive(Debug, Clone)]
enum Dimensions {
    Fullscreen,
    Window { width: u32, height: u32 },
}

impl Dimensions {
    fn args() -> impl Arg<Item = Self> {
        let window = args_depend! {
            opt("", "width", "", ""),
            opt("", "height", "", ""),
        }
        .option_map(|(width, height)| Dimensions::Window { width, height });
        let fullscreen = flag("", "fullscreen", "").some_if(Dimensions::Fullscreen);
        window.choice(fullscreen).required()
    }
}

fn main() {
    let dimensions = Dimensions::args().with_help_default().parse_env_or_exit();
    println!("{:#?}", dimensions);
}

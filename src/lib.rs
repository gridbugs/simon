extern crate either;
extern crate getopts;

use std::str::FromStr;

pub mod ext;
pub mod param;

pub use ext::{ParamExt, ParamOptExt};

use param::*;

pub fn param_req<T: FromStr>(long: &str) -> impl Param<Item = T> {
    param(long, Required)
}
pub fn param_opt<T: FromStr>(long: &str) -> impl Param<Item = Option<T>> {
    param(long, Optional)
}
pub fn param_opt_def<T: FromStr + Clone>(long: &str, def: T) -> impl Param<Item = T> {
    param(long, OptionalWithDefault { default: def })
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn example1() {
        let p = param_req::<i32>("int")
            .map(|i| i + 1)
            .join(param_req::<f32>("float"));
        let (i, f) = p.parse(&["--float", "6.5", "--int", "42"]).unwrap();
        assert_eq!(i, 43);
        assert_eq!(f, 6.5);
    }
    #[derive(Debug, PartialEq, Eq)]
    enum Size {
        Dimensions(i32, i32),
        Fullscreen,
    }
    #[test]
    fn example2() {
        let p_dimensions = param_opt::<i32>("width")
            .opt_join(param_opt::<i32>("height"))
            .opt_map(|(width, height)| Size::Dimensions(width, height));
        let p_fullscreen =
            flag("fullscreen").map(|f| if f { Some(Size::Fullscreen) } else { None });
        let p = p_dimensions.either_same_type(p_fullscreen).required();
        let s = p.parse(&["--width", "4", "--height", "5"]).unwrap();
        assert_eq!(s, Size::Dimensions(4, 5));
    }
}

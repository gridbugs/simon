use std::fmt::{self, Display};

#[derive(Debug, PartialEq, Eq)]
pub enum Never {}

impl Never {
    pub fn result_ok<T>(r: Result<T, Never>) -> T {
        match r {
            Ok(t) => t,
            Err(_) => unreachable!(),
        }
    }
}

impl Display for Never {
    fn fmt(&self, _f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            _ => unreachable!(),
        }
    }
}

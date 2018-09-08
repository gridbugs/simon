use std::fmt::{self, Display};

#[derive(Debug)]
pub enum Either<L, R> {
    Left(L),
    Right(R),
}

impl<T> Either<T, T> {
    pub fn into(self) -> T {
        match self {
            Either::Left(t) | Either::Right(t) => t,
        }
    }
}

impl<L, R> Display for Either<L, R>
where
    L: Display,
    R: Display,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Either::Left(l) => l.fmt(f),
            Either::Right(r) => r.fmt(f),
        }
    }
}

#[derive(Debug)]
pub enum EitherOrBoth<L, R> {
    Either(Either<L, R>),
    Both(L, R),
}

#[derive(Debug)]
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

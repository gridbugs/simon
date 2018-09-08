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

pub enum EitherOrBoth<L, R> {
    Either(Either<L, R>),
    Both(L, R),
}

pub enum Never {}

impl Never {
    pub fn result_ok<T>(r: Result<T, Never>) -> T {
        match r {
            Ok(t) => t,
            Err(_) => unreachable!(),
        }
    }
}

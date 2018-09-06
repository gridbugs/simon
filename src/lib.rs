extern crate getopts;

pub enum SwitchArity {
    Single,
    Multi,
}

pub enum SwitchParam {
    Flag,
    Opt { hint: String },
}

pub struct SwitchCommon {
    pub short: String,
    pub long: String,
    pub doc: String,
}

pub trait Switches {
    fn add(&mut self, common: SwitchCommon, param: SwitchParam, arity: SwitchArity);
}

pub type Matches = getopts::Matches;

pub trait Arg {
    type Item;
    type Error;
    fn update_switches<S: Switches>(&self, switches: &mut S);
    fn name(&self) -> String;
    fn get(&self, matches: &Matches) -> Result<Self::Item, Self::Error>;
    fn map_result<F, U, E>(self, f: F) -> MapResult<Self, F>
    where
        F: Fn(Result<Self::Item, Self::Error>) -> Result<U, E>,
        Self: Sized,
    {
        MapResult { arg: self, f }
    }
    fn both_result<B>(self, b: B) -> BothResult<Self, B>
    where
        B: Arg,
        Self: Sized,
    {
        BothResult { a: self, b }
    }
}

pub struct MapResult<A, F> {
    arg: A,
    f: F,
}

impl<A, F, U, E> Arg for MapResult<A, F>
where
    A: Arg,
    F: Fn(Result<A::Item, A::Error>) -> Result<U, E>,
{
    type Item = U;
    type Error = E;
    fn update_switches<S: Switches>(&self, switches: &mut S) {
        self.arg.update_switches(switches);
    }
    fn name(&self) -> String {
        self.arg.name()
    }
    fn get(&self, matches: &Matches) -> Result<Self::Item, Self::Error> {
        (self.f)(self.arg.get(matches))
    }
}

pub struct BothResult<A, B> {
    a: A,
    b: B,
}

pub enum BothError<A, B> {
    A(A),
    B(B),
}

impl<A, B> Arg for BothResult<A, B>
where
    A: Arg,
    B: Arg,
{
    type Item = (Result<A::Item, A::Error>, Result<B::Item, B::Error>);
    type Error = Never;
    fn update_switches<S: Switches>(&self, switches: &mut S) {
        self.a.update_switches(switches);
        self.b.update_switches(switches);
    }
    fn name(&self) -> String {
        format!("({} and {})", self.a.name(), self.b.name())
    }
    fn get(&self, matches: &Matches) -> Result<Self::Item, Self::Error> {
        Ok((self.a.get(matches), self.b.get(matches)))
    }
}

pub enum Either<L, R> {
    Left(L),
    Right(R),
}

pub enum Never {}

impl Never {
    fn result_ok<T>(r: Result<T, Never>) -> T {
        match r {
            Ok(t) => t,
            Err(_) => unreachable!(),
        }
    }
}

pub enum TryMapError<A, M> {
    Arg(A),
    Map(M),
}

pub struct DependError {
    pub supplied: String,
    pub missing: String,
}

pub type MapError<E> = TryMapError<E, Never>;

pub struct ArgExt<A> {
    arg: A,
}

impl<A> ArgExt<A>
where
    A: Arg,
{
    pub fn map_result<F, U, E>(self, f: F) -> ArgExt<impl Arg<Item = U, Error = E>>
    where
        F: Fn(Result<A::Item, A::Error>) -> Result<U, E>,
    {
        ArgExt {
            arg: Arg::map_result(self.arg, f),
        }
    }
    pub fn both_result<B>(
        self,
        b: ArgExt<B>,
    ) -> ArgExt<
        impl Arg<Item = (Result<A::Item, A::Error>, Result<B::Item, B::Error>), Error = Never>,
    >
    where
        B: Arg,
    {
        ArgExt {
            arg: Arg::both_result(self.arg, b.arg),
        }
    }

    pub fn both<B>(
        self,
        b: ArgExt<B>,
    ) -> ArgExt<impl Arg<Item = (A::Item, B::Item), Error = BothError<A::Error, B::Error>>>
    where
        B: Arg,
    {
        self.both_result(b).map_result(|r| {
            let (a, b) = Never::result_ok(r);
            Ok((a.map_err(BothError::A)?, b.map_err(BothError::B)?))
        })
    }
    pub fn try_map<F, U, E>(
        self,
        f: F,
    ) -> ArgExt<impl Arg<Item = U, Error = TryMapError<A::Error, E>>>
    where
        F: Fn(A::Item) -> Result<U, E>,
    {
        self.map_result(move |r| {
            r.map_err(TryMapError::Arg)
                .and_then(|x| (f)(x).map_err(TryMapError::Map))
        })
    }
    pub fn map<F, U>(self, f: F) -> ArgExt<impl Arg<Item = U, Error = MapError<A::Error>>>
    where
        F: Fn(A::Item) -> U,
    {
        self.try_map(move |x| Ok((f)(x)))
    }
}

impl<A, T> ArgExt<A>
where
    A: Arg<Item = Option<T>>,
{
    pub fn depend<B, U>(self, b: ArgExt<B>) -> ArgExt<impl Arg<Item = Option<(T, U)>>>
    where
        B: Arg<Item = Option<U>>,
    {
        let a_name = self.arg.name();
        let b_name = b.arg.name();
        self.both(b).try_map(move |both| match both {
            (None, None) => Ok(None),
            (Some(a), Some(b)) => Ok(Some((a, b))),
            (Some(_), None) => Err(DependError {
                supplied: a_name.clone(),
                missing: b_name.clone(),
            }),
            (None, Some(_)) => Err(DependError {
                supplied: b_name.clone(),
                missing: a_name.clone(),
            }),
        })
    }
    pub fn otherwise<U>(self, b: ArgExt<U>) -> ArgExt<impl Arg<Item = Either<T, U::Item>>>
    where
        U: Arg,
    {
        self.both_result(b).map_result(|r| {
            let (a, b) = Never::result_ok(r);
            match a.map_err(Either::Left)? {
                Some(a) => Ok(Either::Left(a)),
                None => b.map(Either::Right).map_err(Either::Right),
            }
        })
    }
}

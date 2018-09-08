use arg::*;
use std::fmt::{self, Debug, Display};
use std::iter::FromIterator;
use util::*;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TryMapError<A, M> {
    Arg(A),
    Map(M),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DependError {
    pub supplied: String,
    pub missing: String,
}

pub type MapError<E> = TryMapError<E, Never>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MultipleMutuallyExclusiveArgs(String, String);

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MissingRequiredArg(String);

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConvertFailed<V, E> {
    name: String,
    error: E,
    value: V,
}

impl<A, M> Display for TryMapError<A, M>
where
    A: Display,
    M: Display,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            TryMapError::Arg(a) => a.fmt(f),
            TryMapError::Map(m) => m.fmt(f),
        }
    }
}

impl Display for DependError {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(
            f,
            "{} and {} must be supplied together or not at all ({} is supplied, {} is \
             missing)",
            self.supplied, self.missing, self.supplied, self.missing
        )
    }
}

impl Display for MultipleMutuallyExclusiveArgs {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(
            f,
            "{} and {} are mutually exclusive but both were supplied",
            self.0, self.1
        )
    }
}

impl Display for MissingRequiredArg {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "{} is required but not supplied", self.0)
    }
}

impl<V, E> Display for ConvertFailed<V, E>
where
    V: Display,
    E: Display,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(
            f,
            "invalid value \"{}\" supplied for \"{}\" ({})",
            self.value, self.name, self.error
        )
    }
}

pub struct ArgExt<A> {
    arg: A,
}

impl<A> Arg for ArgExt<A>
where
    A: Arg,
{
    type Item = A::Item;
    type Error = A::Error;
    fn update_switches<S: Switches>(&self, switches: &mut S) {
        self.arg.update_switches(switches);
    }
    fn name(&self) -> String {
        self.arg.name()
    }
    fn get(&self, matches: &Matches) -> Result<Self::Item, Self::Error> {
        self.arg.get(matches)
    }
}

impl<A> ArgExt<A>
where
    A: Arg,
{
    pub fn result_map<F, U, E>(self, f: F) -> ArgExt<impl Arg<Item = U, Error = E>>
    where
        F: Fn(Result<A::Item, A::Error>) -> Result<U, E>,
        E: Debug + Display,
    {
        ArgExt {
            arg: Arg::result_map(self.arg, f),
        }
    }
    pub fn result_both<B>(
        self,
        b: B,
    ) -> ArgExt<
        impl Arg<Item = (Result<A::Item, A::Error>, Result<B::Item, B::Error>), Error = Never>,
    >
    where
        B: Arg,
    {
        ArgExt {
            arg: Arg::result_both(self.arg, b),
        }
    }

    pub fn both<B>(
        self,
        b: B,
    ) -> ArgExt<impl Arg<Item = (A::Item, B::Item), Error = BothError<A::Error, B::Error>>>
    where
        B: Arg,
    {
        self.result_both(b).result_map(|r| {
            let (a, b) = Never::result_ok(r);
            Ok((a.map_err(BothError::A)?, b.map_err(BothError::B)?))
        })
    }
    pub fn try_map<F, U, E>(
        self,
        f: F,
    ) -> ArgExt<impl Arg<Item = U, Error = TryMapError<A::Error, E>>>
    where
        E: Debug + Display,
        F: Fn(A::Item) -> Result<U, E>,
    {
        self.result_map(move |r| {
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
    pub fn convert<F, U, E>(
        self,
        f: F,
    ) -> ArgExt<
        impl Arg<Item = U, Error = TryMapError<A::Error, ConvertFailed<A::Item, E>>>,
    >
    where
        A::Item: Clone + Debug + Display,
        E: Clone + Debug + Display,
        F: Fn(A::Item) -> Result<U, E>,
    {
        let name = self.name();
        self.try_map(move |value| {
            let name = name.clone();
            f(value.clone()).map_err(move |error| ConvertFailed { error, name, value })
        })
    }
}

impl<A, T> ArgExt<A>
where
    A: Arg<Item = Option<T>>,
{
    pub fn depend<B, U>(self, b: B) -> ArgExt<impl Arg<Item = Option<(T, U)>>>
    where
        B: Arg<Item = Option<U>>,
    {
        let a_name = self.name();
        let b_name = b.name();
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
    pub fn otherwise<U>(self, b: U) -> ArgExt<impl Arg<Item = Either<T, U::Item>>>
    where
        U: Arg,
    {
        self.result_both(b).result_map(|r| {
            let (a, b) = Never::result_ok(r);
            match a.map_err(Either::Left)? {
                Some(a) => Ok(Either::Left(a)),
                None => b.map(Either::Right).map_err(Either::Right),
            }
        })
    }
    pub fn option_try_map<F, U, E>(
        self,
        f: F,
    ) -> ArgExt<impl Arg<Item = Option<U>, Error = TryMapError<A::Error, E>>>
    where
        E: Debug + Display,
        F: Fn(T) -> Result<U, E>,
    {
        self.try_map(move |x| match x {
            None => Ok(None),
            Some(x) => f(x).map(Some),
        })
    }
    pub fn option_map<F, U>(self, f: F) -> ArgExt<impl Arg<Item = Option<U>>>
    where
        F: Fn(T) -> U,
    {
        self.map(move |x| x.map(&f))
    }
    pub fn either_or_both_any<B, U>(
        self,
        b: B,
    ) -> ArgExt<impl Arg<Item = Option<EitherOrBoth<T, U>>>>
    where
        B: Arg<Item = Option<U>>,
    {
        self.both(b).map(move |both| match both {
            (None, None) => None,
            (Some(l), None) => Some(EitherOrBoth::Either(Either::Left(l))),
            (None, Some(r)) => Some(EitherOrBoth::Either(Either::Right(r))),
            (Some(l), Some(r)) => Some(EitherOrBoth::Both(l, r)),
        })
    }
    pub fn either_any<B, U>(self, b: B) -> ArgExt<impl Arg<Item = Option<Either<T, U>>>>
    where
        B: Arg<Item = Option<U>>,
    {
        let a_name = self.name();
        let b_name = b.name();
        self.either_or_both_any(b)
            .option_try_map(move |either_or_both| match either_or_both {
                EitherOrBoth::Either(e) => Ok(e),
                EitherOrBoth::Both(_, _) => Err(MultipleMutuallyExclusiveArgs(
                    a_name.clone(),
                    b_name.clone(),
                )),
            })
    }
    pub fn either<B>(self, b: B) -> ArgExt<impl Arg<Item = Option<T>>>
    where
        B: Arg<Item = Option<T>>,
    {
        self.either_any(b).option_map(Either::into)
    }
    pub fn with_default(self, t: T) -> ArgExt<impl Arg<Item = T>>
    where
        T: Clone,
    {
        self.map(move |x| x.unwrap_or(t.clone()))
    }
    pub fn required(self) -> ArgExt<impl Arg<Item = T>> {
        let name = self.name();
        self.try_map(move |x| match x {
            Some(x) => Ok(x),
            None => Err(MissingRequiredArg(name.clone())),
        })
    }
    pub fn option_convert<F, U, E>(
        self,
        f: F,
    ) -> ArgExt<
        impl Arg<Item = Option<U>, Error = TryMapError<A::Error, ConvertFailed<T, E>>>,
    >
    where
        T: Clone + Debug + Display,
        E: Clone + Debug + Display,
        F: Fn(T) -> Result<U, E>,
    {
        let name = self.name();
        self.option_try_map(move |value| {
            let name = name.clone();
            f(value.clone()).map_err(move |error| ConvertFailed { error, name, value })
        })
    }
}

impl<A> ArgExt<A>
where
    A: Arg<Item = bool>,
{
    pub fn some_if<T>(self, t: T) -> ArgExt<impl Arg<Item = Option<T>>>
    where
        T: Clone,
    {
        self.map(move |b| if b { Some(t.clone()) } else { None })
    }
    pub fn unit_option(self) -> ArgExt<impl Arg<Item = Option<()>>> {
        self.map(|b| if b { Some(()) } else { None })
    }
}

impl<A, I> ArgExt<A>
where
    A: Arg<Item = I>,
    I: IntoIterator,
{
    pub fn into_iter(self) -> ArgExt<impl Arg<Item = I::IntoIter>> {
        self.map(|i| i.into_iter())
    }
    pub fn vec_try_map<F, U, E>(
        self,
        f: F,
    ) -> ArgExt<impl Arg<Item = Vec<U>, Error = TryMapError<A::Error, E>>>
    where
        E: Debug + Display,
        F: Fn(I::Item) -> Result<U, E>,
    {
        self.try_map(move |i| {
            let mut vec = Vec::new();
            for x in i {
                vec.push(f(x)?);
            }
            Ok(vec)
        })
    }
    pub fn vec_map<F, U>(
        self,
        f: F,
    ) -> ArgExt<impl Arg<Item = Vec<U>, Error = MapError<A::Error>>>
    where
        F: Fn(I::Item) -> U,
    {
        self.vec_try_map(move |x| Ok(f(x)))
    }
    pub fn vec_convert<F, U, E>(
        self,
        f: F,
    ) -> ArgExt<
        impl Arg<Item = Vec<U>, Error = TryMapError<A::Error, ConvertFailed<I::Item, E>>>,
    >
    where
        I::Item: Clone + Debug + Display,
        E: Clone + Debug + Display,
        F: Fn(I::Item) -> Result<U, E>,
    {
        let name = self.name();
        self.vec_try_map(move |value| {
            let name = name.clone();
            f(value.clone()).map_err(move |error| ConvertFailed { error, name, value })
        })
    }
}

impl<A, I, T, E> ArgExt<A>
where
    E: Debug + Display,
    A: Arg<Item = I>,
    I: IntoIterator<Item = Result<T, E>>,
{
    pub fn vec_ok_or_first_err(
        self,
    ) -> ArgExt<impl Arg<Item = Vec<T>, Error = TryMapError<A::Error, E>>> {
        self.try_map(|i| {
            let mut vec = Vec::new();
            for x in i {
                vec.push(x?);
            }
            Ok(vec)
        })
    }
}

impl<A, I> ArgExt<A>
where
    A: Arg<Item = I>,
    I: Iterator,
{
    pub fn collect<C>(self) -> ArgExt<impl Arg<Item = C>>
    where
        C: FromIterator<I::Item>,
    {
        self.map(|i| i.collect())
    }
}

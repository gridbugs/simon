use std::iter;
use super::*;

#[derive(Debug, PartialEq, Eq)]
pub enum ChildErrorOr<C, E> {
    Child(C),
    Error(E),
}

impl<C: Display, E: Display> Display for ChildErrorOr<C, E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            ChildErrorOr::Child(e) => fmt::Display::fmt(&e, f),
            ChildErrorOr::Error(e) => fmt::Display::fmt(&e, f),
        }
    }
}

pub struct Map<A, F> {
    pub(crate) arg: A,
    pub(crate) f: F,
}

impl<A, U, F> Arg for Map<A, F>
where
    A: Arg,
    F: Fn(A::Item) -> U,
{
    type Item = U;
    type Error = A::Error;
    fn update_options<O: Options>(&self, opts: &mut O) {
        self.arg.update_options(opts);
    }
    fn name(&self) -> String {
        self.arg.name()
    }
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error> {
        self.arg.get(matches).map(&self.f)
    }
}

pub enum HelpOr<T> {
    Help,
    Value(T),
}

pub struct WithHelp<V> {
    pub(crate) cond: Flag,
    pub(crate) value: V,
}

impl<V> Arg for WithHelp<V>
where
    V: Arg,
{
    type Item = HelpOr<V::Item>;
    type Error = V::Error;
    fn update_options<O: Options>(&self, opts: &mut O) {
        self.cond.update_options(opts);
        self.value.update_options(opts);
    }
    fn name(&self) -> String {
        self.value.name()
    }
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error> {
        if Never::result_ok(self.cond.get(matches)) {
            Ok(HelpOr::Help)
        } else {
            Ok(HelpOr::Value(self.value.get(matches)?))
        }
    }
}

pub struct Otherwise<C, V> {
    pub(crate) cond: C,
    pub(crate) value: V,
}

impl<T, C, V> Arg for Otherwise<C, V>
where
    C: Arg<Item = Option<T>>,
    V: Arg,
{
    type Item = Either<T, V::Item>;
    type Error = Either<C::Error, V::Error>;
    fn update_options<O: Options>(&self, opts: &mut O) {
        self.cond.update_options(opts);
        self.value.update_options(opts);
    }
    fn name(&self) -> String {
        self.value.name()
    }
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error> {
        match self.cond.get(matches) {
            Err(e) => Err(Either::Left(e)),
            Ok(o) => match o {
                Some(t) => Ok(Either::Left(t)),
                None => match self.value.get(matches) {
                    Err(e) => Err(Either::Right(e)),
                    Ok(o) => Ok(Either::Right(o)),
                },
            },
        }
    }
}

pub struct SomeIf<A, T> {
    pub(crate) arg: A,
    pub(crate) value: T,
}

impl<A, T> Arg for SomeIf<A, T>
where
    T: Clone,
    A: Arg<Item = bool>,
{
    type Item = Option<T>;
    type Error = A::Error;
    fn update_options<O: Options>(&self, opts: &mut O) {
        self.arg.update_options(opts);
    }
    fn name(&self) -> String {
        self.arg.name()
    }
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error> {
        Ok(if self.arg.get(matches)? {
            Some(self.value.clone())
        } else {
            None
        })
    }
}

pub struct TryMap<A, F> {
    pub(crate) arg: A,
    pub(crate) f: F,
}

impl<A, U, E, F> Arg for TryMap<A, F>
where
    A: Arg,
    E: Debug + Display + Eq,
    F: Fn(A::Item) -> Result<U, E>,
{
    type Item = U;
    type Error = ChildErrorOr<A::Error, E>;
    fn update_options<O: Options>(&self, opts: &mut O) {
        self.arg.update_options(opts);
    }
    fn name(&self) -> String {
        self.arg.name()
    }
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error> {
        self.arg
            .get(matches)
            .map_err(ChildErrorOr::Child)
            .and_then(|o| (self.f)(o).map_err(ChildErrorOr::Error))
    }
}

pub struct OptionMap<A, F> {
    pub(crate) arg: A,
    pub(crate) f: F,
}

impl<A, T, U, F> Arg for OptionMap<A, F>
where
    A: Arg<Item = Option<T>>,
    F: Fn(T) -> U,
{
    type Item = Option<U>;
    type Error = A::Error;
    fn update_options<O: Options>(&self, opts: &mut O) {
        self.arg.update_options(opts);
    }
    fn name(&self) -> String {
        self.arg.name()
    }
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error> {
        self.arg.get(matches).map(|v| v.map(&self.f))
    }
}

pub struct OptionTryMap<A, F> {
    pub(crate) arg: A,
    pub(crate) f: F,
}

impl<T, A, U, E, F> Arg for OptionTryMap<A, F>
where
    A: Arg<Item = Option<T>>,
    E: Debug + Display + Eq,
    F: Fn(T) -> Result<U, E>,
{
    type Item = Option<U>;
    type Error = ChildErrorOr<A::Error, E>;
    fn update_options<O: Options>(&self, opts: &mut O) {
        self.arg.update_options(opts);
    }
    fn name(&self) -> String {
        self.arg.name()
    }
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error> {
        self.arg
            .get(matches)
            .map_err(ChildErrorOr::Child)
            .and_then(|o| match o {
                Some(t) => (self.f)(t).map(Some).map_err(ChildErrorOr::Error),
                None => Ok(None),
            })
    }
}

pub struct Join<A, B> {
    pub(crate) a: A,
    pub(crate) b: B,
}

pub type JoinError<A, B> = Either<A, B>;

impl<A, B> Arg for Join<A, B>
where
    A: Arg,
    B: Arg,
{
    type Item = (A::Item, B::Item);
    type Error = JoinError<A::Error, B::Error>;
    fn update_options<O: Options>(&self, opts: &mut O) {
        self.a.update_options(opts);
        self.b.update_options(opts);
    }
    fn name(&self) -> String {
        format!("({} and {})", self.a.name(), self.b.name())
    }
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error> {
        Ok((
            self.a.get(matches).map_err(Either::Left)?,
            self.b.get(matches).map_err(Either::Right)?,
        ))
    }
}

pub struct OptionJoin<A, B> {
    pub(crate) a: A,
    pub(crate) b: B,
}

#[derive(Debug, PartialEq, Eq)]
pub enum OptionJoinError<A, B> {
    Left(A),
    Right(B),
    MissingOptionJoinantArg {
        supplied_name: String,
        missing_name: String,
    },
}

impl<A: Display, B: Display> Display for OptionJoinError<A, B> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            OptionJoinError::Left(a) => fmt::Display::fmt(&a, f),
            OptionJoinError::Right(b) => fmt::Display::fmt(&b, f),
            OptionJoinError::MissingOptionJoinantArg {
                supplied_name,
                missing_name,
            } => write!(
                f,
                "{} and {} must be supplied together or not at all \
                 ({} is supplied, {} is missing)",
                supplied_name, missing_name, supplied_name, missing_name
            ),
        }
    }
}

impl<T, U, A, B> Arg for OptionJoin<A, B>
where
    A: Arg<Item = Option<T>>,
    B: Arg<Item = Option<U>>,
{
    type Item = Option<(T, U)>;
    type Error = OptionJoinError<A::Error, B::Error>;
    fn update_options<O: Options>(&self, opts: &mut O) {
        self.a.update_options(opts);
        self.b.update_options(opts);
    }
    fn name(&self) -> String {
        format!("({} and {})", self.a.name(), self.b.name())
    }
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error> {
        let maybe_a = self.a.get(matches).map_err(OptionJoinError::Left)?;
        let maybe_b = self.b.get(matches).map_err(OptionJoinError::Right)?;
        match (maybe_a, maybe_b) {
            (Some(a), Some(b)) => Ok(Some((a, b))),
            (None, None) => Ok(None),
            (Some(_), None) => Err(OptionJoinError::MissingOptionJoinantArg {
                supplied_name: self.a.name(),
                missing_name: self.b.name(),
            }),
            (None, Some(_)) => Err(OptionJoinError::MissingOptionJoinantArg {
                supplied_name: self.b.name(),
                missing_name: self.a.name(),
            }),
        }
    }
}

pub struct EitherCombinator<A, B> {
    pub(crate) a: A,
    pub(crate) b: B,
}

#[derive(Debug, PartialEq, Eq)]
pub enum EitherError<A, B> {
    Left(A),
    Right(B),
    MultipleMutuallyExclusiveArgs {
        left_name: String,
        right_name: String,
    },
}

impl<A: Display, B: Display> Display for EitherError<A, B> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            EitherError::Left(a) => fmt::Display::fmt(&a, f),
            EitherError::Right(b) => fmt::Display::fmt(&b, f),
            EitherError::MultipleMutuallyExclusiveArgs {
                left_name,
                right_name,
            } => write!(
                f,
                "{} and {} are mutually exclusive but both were supplied",
                left_name, right_name
            ),
        }
    }
}

fn either_update_options(a: &impl Arg, b: &impl Arg, opts: &mut impl Options) {
    a.update_options(opts);
    b.update_options(opts);
}

impl<T, U, A, B> Arg for EitherCombinator<A, B>
where
    A: Arg<Item = Option<T>>,
    B: Arg<Item = Option<U>>,
{
    type Item = Option<Either<T, U>>;
    type Error = EitherError<A::Error, B::Error>;
    fn update_options<O: Options>(&self, opts: &mut O) {
        either_update_options(&self.a, &self.b, opts);
    }
    fn name(&self) -> String {
        format!("({} or {})", self.a.name(), self.b.name())
    }
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error> {
        let maybe_a = self.a.get(matches).map_err(EitherError::Left)?;
        let maybe_b = self.b.get(matches).map_err(EitherError::Right)?;
        match (maybe_a, maybe_b) {
            (Some(_), Some(_)) => Err(EitherError::MultipleMutuallyExclusiveArgs {
                left_name: self.a.name(),
                right_name: self.b.name(),
            }),
            (Some(a), None) => Ok(Some(Either::Left(a))),
            (None, Some(b)) => Ok(Some(Either::Right(b))),
            (None, None) => Ok(None),
        }
    }
}

pub struct EitherHomogeneous<A, B> {
    pub(crate) a: A,
    pub(crate) b: B,
}

impl<T, A, B> Arg for EitherHomogeneous<A, B>
where
    A: Arg<Item = Option<T>>,
    B: Arg<Item = Option<T>>,
{
    type Item = Option<T>;
    type Error = EitherError<A::Error, B::Error>;
    fn update_options<O: Options>(&self, opts: &mut O) {
        either_update_options(&self.a, &self.b, opts);
    }
    fn name(&self) -> String {
        format!("({} or {})", self.a.name(), self.b.name())
    }
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error> {
        let maybe_a = self.a.get(matches).map_err(EitherError::Left)?;
        let maybe_b = self.b.get(matches).map_err(EitherError::Right)?;
        match (maybe_a, maybe_b) {
            (Some(_), Some(_)) => Err(EitherError::MultipleMutuallyExclusiveArgs {
                left_name: self.a.name(),
                right_name: self.b.name(),
            }),
            (Some(a), None) => Ok(Some(a)),
            (None, Some(b)) => Ok(Some(b)),
            (None, None) => Ok(None),
        }
    }
}

pub struct WithDefault<P, T> {
    pub(crate) arg: P,
    pub(crate) default: T,
}

impl<P, T> Arg for WithDefault<P, T>
where
    T: Clone,
    P: Arg<Item = Option<T>>,
{
    type Item = T;
    type Error = P::Error;
    fn update_options<O: Options>(&self, opts: &mut O) {
        self.arg.update_options(opts);
    }
    fn name(&self) -> String {
        self.arg.name()
    }
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error> {
        Ok(self.arg
            .get(matches)?
            .unwrap_or_else(|| self.default.clone()))
    }
}

pub struct Required<P> {
    pub(crate) arg: P,
}

#[derive(Debug, PartialEq, Eq)]
pub enum RequiredError<E> {
    Other(E),
    MissingRequiredArg { name: String },
}

impl<E: Display> Display for RequiredError<E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            RequiredError::Other(e) => fmt::Display::fmt(&e, f),
            RequiredError::MissingRequiredArg { name } => {
                write!(f, "{} is required but not supplied", name)
            }
        }
    }
}

impl<P, T> Arg for Required<P>
where
    P: Arg<Item = Option<T>>,
{
    type Item = T;
    type Error = RequiredError<P::Error>;
    fn update_options<O: Options>(&self, opts: &mut O) {
        self.arg.update_options(opts);
    }
    fn name(&self) -> String {
        self.arg.name()
    }
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error> {
        self.arg.get(matches).map_err(RequiredError::Other)?.ok_or(
            RequiredError::MissingRequiredArg {
                name: self.arg.name(),
            },
        )
    }
}

pub struct Convert<A, F> {
    pub(crate) arg: A,
    pub(crate) f: F,
}

#[derive(Debug, PartialEq, Eq)]
pub enum ConvertError<O, T, E> {
    Other(O),
    ConversionFailed { name: String, error: E, value: T },
}

impl<O: Display, T: Display, E: Display> Display for ConvertError<O, T, E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            ConvertError::Other(e) => fmt::Display::fmt(&e, f),
            ConvertError::ConversionFailed { name, error, value } => write!(
                f,
                "invalid value \"{}\" supplied for \"{}\" ({})",
                value, name, error
            ),
        }
    }
}

impl<A, F, U, E> Arg for Convert<A, F>
where
    A: Arg,
    A::Item: Clone + Debug + Display + Eq,
    E: Debug + Display + Eq,
    F: Fn(&A::Item) -> Result<U, E>,
{
    type Item = U;
    type Error = ConvertError<A::Error, A::Item, E>;
    fn update_options<O: Options>(&self, opts: &mut O) {
        self.arg.update_options(opts);
    }
    fn name(&self) -> String {
        self.arg.name()
    }
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error> {
        self.arg
            .get(matches)
            .map_err(ConvertError::Other)
            .and_then(|o| {
                (self.f)(&o).map_err(|error| ConvertError::ConversionFailed {
                    name: self.arg.name(),
                    value: o,
                    error,
                })
            })
    }
}

pub struct OptConvert<A, F> {
    pub(crate) arg: A,
    pub(crate) f: F,
}

impl<T, A, U, F, E> Arg for OptConvert<A, F>
where
    T: Clone + Debug + Display + Eq,
    E: Clone + Debug + Display + Eq,
    A: Arg<Item = Option<T>>,
    F: Fn(T) -> Result<U, E>,
{
    type Item = Option<U>;
    type Error = ConvertError<A::Error, T, E>;
    fn update_options<O: Options>(&self, opts: &mut O) {
        self.arg.update_options(opts);
    }
    fn name(&self) -> String {
        self.arg.name()
    }
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error> {
        self.arg
            .get(matches)
            .map_err(ConvertError::Other)
            .and_then(|o| match o {
                Some(t) => (self.f)(t.clone()).map(Some).map_err(|error| {
                    ConvertError::ConversionFailed {
                        name: self.arg.name(),
                        value: t,
                        error,
                    }
                }),
                None => Ok(None),
            })
    }
}

pub struct Rename<P> {
    pub(crate) arg: P,
    pub(crate) name: String,
}

impl<P> Arg for Rename<P>
where
    P: Arg,
{
    type Item = P::Item;
    type Error = P::Error;

    fn update_options<O: Options>(&self, opts: &mut O) {
        self.arg.update_options(opts);
    }
    fn name(&self) -> String {
        self.name.clone()
    }
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error> {
        self.arg.get(matches)
    }
}

pub struct Value<T> {
    pub(crate) name: String,
    pub(crate) value: T,
}

impl<T> Arg for Value<T>
where
    T: Clone,
{
    type Item = T;
    type Error = Never;
    fn update_options<O: Options>(&self, _opts: &mut O) {}
    fn name(&self) -> String {
        self.name.clone()
    }
    fn get(&self, _matches: &getopts::Matches) -> Result<Self::Item, Self::Error> {
        Ok(self.value.clone())
    }
}

impl<T: Clone> Value<T> {
    pub fn new(value: T, name: &str) -> Value<T> {
        Self {
            value,
            name: name.to_string(),
        }
    }
}

pub type UnitOption<T> = SomeIf<T, ()>;

pub struct IterCombinator<A> {
    pub(crate) arg: A,
}

impl<I, A> Arg for IterCombinator<A>
where
    I: IntoIterator,
    A: Arg<Item = I>,
{
    type Item = I::IntoIter;
    type Error = A::Error;
    fn update_options<O: Options>(&self, opts: &mut O) {
        self.arg.update_options(opts)
    }
    fn name(&self) -> String {
        self.arg.name()
    }
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error> {
        Ok(self.arg.get(matches)?.into_iter())
    }
}

pub struct IterConvert<'a, A, F: 'a, U, E>
where
    A: Arg,
    A::Item: Iterator,
    F: Fn(<A::Item as Iterator>::Item) -> Result<U, E>,
{
    pub(crate) arg: A,
    pub(crate) f: &'a F,
}

impl<'a, I, A, F, U, E> Arg for IterConvert<'a, A, F, U, E>
where
    I: Iterator,
    A: Arg<Item = I>,
    F: Fn(I::Item) -> Result<U, E>,
{
    type Item = iter::Map<I, &'a F>;
    type Error = A::Error;
    fn update_options<O: Options>(&self, opts: &mut O) {
        self.arg.update_options(opts)
    }
    fn name(&self) -> String {
        self.arg.name()
    }
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error> {
        Ok(self.arg.get(matches)?.map(self.f))
    }
}

pub struct IterOkVec<A> {
    pub(crate) arg: A,
}

#[derive(Debug, PartialEq, Eq)]
pub enum IterOkVecError<O, E> {
    Other(O),
    ErrorInIter { name: String, error: E },
}

impl<O: Display, E: Display> Display for IterOkVecError<O, E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            IterOkVecError::Other(e) => fmt::Display::fmt(&e, f),
            IterOkVecError::ErrorInIter { name, error } => write!(f, "{}: {}", name, error),
        }
    }
}

impl<I, A, T, E> Arg for IterOkVec<A>
where
    E: Debug + Display + Eq,
    I: Iterator<Item = Result<T, E>>,
    A: Arg<Item = I>,
{
    type Item = Vec<T>;
    type Error = IterOkVecError<A::Error, E>;
    fn update_options<O: Options>(&self, opts: &mut O) {
        self.arg.update_options(opts)
    }
    fn name(&self) -> String {
        self.arg.name()
    }
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error> {
        let mut vec = Vec::new();
        for x in self.arg.get(matches).map_err(IterOkVecError::Other)? {
            match x {
                Ok(o) => vec.push(o),
                Err(error) => {
                    return Err(IterOkVecError::ErrorInIter {
                        name: self.name(),
                        error,
                    })
                }
            }
        }
        Ok(vec)
    }
}

pub type IterConvertOkVec<'a, T, F, U, E> = IterOkVec<IterConvert<'a, T, F, U, E>>;
pub type IntoIterConvertOkVec<'a, T, F, U, E> = IterConvertOkVec<'a, IterCombinator<T>, F, U, E>;

pub struct Valid<A> {
    pub(crate) arg: A,
}

impl<A> Arg for Valid<A>
where
    A: Arg,
{
    type Item = A::Item;
    type Error = ChildErrorOr<A::Error, Invalid>;
    fn update_options<O: Options>(&self, opts: &mut O) {
        self.arg.update_options(opts)
    }
    fn name(&self) -> String {
        self.arg.name()
    }
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error> {
        if let Some(invalid) = self.validate() {
            Err(ChildErrorOr::Error(invalid))
        } else {
            self.arg.get(matches).map_err(ChildErrorOr::Child)
        }
    }
    fn parse<I>(&self, args: I) -> (Result<Self::Item, TopLevelError<Self::Error>>, Usage)
    where
        I: IntoIterator,
        I::Item: AsRef<OsStr>,
    {
        parse_ignore_validation(self, args)
    }
}

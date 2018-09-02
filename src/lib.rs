extern crate either;
extern crate getopts;

use std::str::FromStr;
use std::fmt::{self, Debug, Display};
use std::ffi::OsStr;

pub trait ParamError: Debug + Display {}

#[derive(Debug)]
pub enum TopLevelError<E> {
    Getopts(getopts::Fail),
    Other(E),
}

impl<E: ParamError> Display for TopLevelError<E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            TopLevelError::Getopts(fail) => fmt::Display::fmt(&fail, f),
            TopLevelError::Other(other) => fmt::Display::fmt(&other, f),
        }
    }
}

impl<E: ParamError> ParamError for TopLevelError<E> {}

impl<T> From<getopts::Fail> for TopLevelError<T> {
    fn from(f: getopts::Fail) -> Self {
        TopLevelError::Getopts(f)
    }
}

pub trait Param {
    type Item;
    type Error: ParamError;
    fn update_options(&self, opts: &mut getopts::Options);
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error>;
    fn name(&self) -> String;
    fn parse<C: IntoIterator>(&self, args: C) -> Result<Self::Item, TopLevelError<Self::Error>>
    where
        C::Item: AsRef<OsStr>,
    {
        let mut opts = getopts::Options::new();
        self.update_options(&mut opts);
        self.get(&opts.parse(args)?).map_err(TopLevelError::Other)
    }
}

#[derive(Default)]
pub struct Arg {
    pub short: String,
    pub long: String,
    pub hint: String,
    pub doc: String,
}

#[derive(Default)]
pub struct Flag {
    pub short: String,
    pub long: String,
    pub doc: String,
}

#[derive(Debug)]
pub enum Never {}

impl Display for Never {
    fn fmt(&self, _f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            _ => unreachable!(),
        }
    }
}

impl ParamError for Never {}

impl Param for Arg {
    type Item = Option<String>;
    type Error = Never;
    fn update_options(&self, opts: &mut getopts::Options) {
        opts.optopt(
            self.short.as_str(),
            self.long.as_str(),
            self.doc.as_str(),
            self.hint.as_str(),
        );
    }
    fn name(&self) -> String {
        self.long.clone()
    }
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error> {
        Ok(matches.opt_str(self.long.as_str()))
    }
}

impl Param for Flag {
    type Item = bool;
    type Error = Never;
    fn update_options(&self, opts: &mut getopts::Options) {
        opts.optflag(self.short.as_str(), self.long.as_str(), self.doc.as_str());
    }
    fn name(&self) -> String {
        self.long.clone()
    }
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error> {
        Ok(matches.opt_present(self.long.as_str()))
    }
}

pub struct Map<A, F> {
    param: A,
    f: F,
}

impl<A, U, F> Param for Map<A, F>
where
    A: Param,
    F: Fn(A::Item) -> U,
{
    type Item = U;
    type Error = A::Error;
    fn update_options(&self, opts: &mut getopts::Options) {
        self.param.update_options(opts);
    }
    fn name(&self) -> String {
        self.param.name()
    }
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error> {
        self.param.get(matches).map(&self.f)
    }
}

pub struct SomeIf<A, T> {
    param: A,
    value: T,
}

impl<A, T> Param for SomeIf<A, T>
where
    T: Clone,
    A: Param<Item = bool>,
{
    type Item = Option<T>;
    type Error = A::Error;
    fn update_options(&self, opts: &mut getopts::Options) {
        self.param.update_options(opts);
    }
    fn name(&self) -> String {
        self.param.name()
    }
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error> {
        Ok(if self.param.get(matches)? {
            Some(self.value.clone())
        } else {
            None
        })
    }
}

pub struct TryMap<A, F> {
    param: A,
    f: F,
}

#[derive(Debug)]
pub enum TryMapError<E, F> {
    Other(E),
    MapFailed(F),
}

impl<E: ParamError, F: Debug + Display> Display for TryMapError<E, F> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            TryMapError::MapFailed(fail) => fmt::Display::fmt(&fail, f),
            TryMapError::Other(other) => fmt::Display::fmt(&other, f),
        }
    }
}

impl<E: ParamError, F: Debug + Display> ParamError for TryMapError<E, F> {}

impl<A, U, E, F> Param for TryMap<A, F>
where
    A: Param,
    E: Debug + Display,
    F: Fn(A::Item) -> Result<U, E>,
{
    type Item = U;
    type Error = TryMapError<A::Error, E>;
    fn update_options(&self, opts: &mut getopts::Options) {
        self.param.update_options(opts);
    }
    fn name(&self) -> String {
        self.param.name()
    }
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error> {
        self.param
            .get(matches)
            .map_err(TryMapError::Other)
            .and_then(|o| (self.f)(o).map_err(TryMapError::MapFailed))
    }
}

pub struct OptMap<A, F> {
    param: A,
    f: F,
}

impl<A, T, U, F> Param for OptMap<A, F>
where
    A: Param<Item = Option<T>>,
    F: Fn(T) -> U,
{
    type Item = Option<U>;
    type Error = A::Error;
    fn update_options(&self, opts: &mut getopts::Options) {
        self.param.update_options(opts);
    }
    fn name(&self) -> String {
        self.param.name()
    }
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error> {
        self.param.get(matches).map(|v| v.map(&self.f))
    }
}

pub struct OptTryMap<A, F> {
    param: A,
    f: F,
}

impl<T, A, U, E, F> Param for OptTryMap<A, F>
where
    A: Param<Item = Option<T>>,
    E: Debug + Display,
    F: Fn(T) -> Result<U, E>,
{
    type Item = Option<U>;
    type Error = TryMapError<A::Error, E>;
    fn update_options(&self, opts: &mut getopts::Options) {
        self.param.update_options(opts);
    }
    fn name(&self) -> String {
        self.param.name()
    }
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error> {
        self.param
            .get(matches)
            .map_err(TryMapError::Other)
            .and_then(|o| match o {
                Some(t) => (self.f)(t).map(Some).map_err(TryMapError::MapFailed),
                None => Ok(None),
            })
    }
}

pub struct Join<A, B> {
    a: A,
    b: B,
}

pub type JoinError<A, B> = either::Either<A, B>;

impl<A: ParamError, B: ParamError> ParamError for JoinError<A, B> {}

impl<A, B> Param for Join<A, B>
where
    A: Param,
    B: Param,
{
    type Item = (A::Item, B::Item);
    type Error = JoinError<A::Error, B::Error>;
    fn update_options(&self, opts: &mut getopts::Options) {
        self.a.update_options(opts);
        self.b.update_options(opts);
    }
    fn name(&self) -> String {
        format!("({} and {})", self.a.name(), self.b.name())
    }
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error> {
        Ok((
            self.a.get(matches).map_err(either::Left)?,
            self.b.get(matches).map_err(either::Right)?,
        ))
    }
}

pub struct Codepend<A, B> {
    a: A,
    b: B,
}

#[derive(Debug)]
pub enum CodependError<A, B> {
    Left(A),
    Right(B),
    MissingCodependantParam {
        supplied_name: String,
        missing_name: String,
    },
}

impl<A: ParamError, B: ParamError> Display for CodependError<A, B> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            CodependError::Left(a) => fmt::Display::fmt(&a, f),
            CodependError::Right(b) => fmt::Display::fmt(&b, f),
            CodependError::MissingCodependantParam {
                supplied_name,
                missing_name,
            } => write!(
                f,
                "{} and {} must be supplied together or not at all ({} is supplied, {} is missing)",
                supplied_name, missing_name, supplied_name, missing_name
            ),
        }
    }
}

impl<A: ParamError, B: ParamError> ParamError for CodependError<A, B> {}

impl<T, U, A, B> Param for Codepend<A, B>
where
    A: Param<Item = Option<T>>,
    B: Param<Item = Option<U>>,
{
    type Item = Option<(T, U)>;
    type Error = CodependError<A::Error, B::Error>;
    fn update_options(&self, opts: &mut getopts::Options) {
        self.a.update_options(opts);
        self.b.update_options(opts);
    }
    fn name(&self) -> String {
        format!("({} and {})", self.a.name(), self.b.name())
    }
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error> {
        let maybe_a = self.a.get(matches).map_err(CodependError::Left)?;
        let maybe_b = self.b.get(matches).map_err(CodependError::Right)?;
        match (maybe_a, maybe_b) {
            (Some(a), Some(b)) => Ok(Some((a, b))),
            (None, None) => Ok(None),
            (Some(_), None) => Err(CodependError::MissingCodependantParam {
                supplied_name: self.a.name(),
                missing_name: self.b.name(),
            }),
            (None, Some(_)) => Err(CodependError::MissingCodependantParam {
                supplied_name: self.b.name(),
                missing_name: self.a.name(),
            }),
        }
    }
}

pub struct Either<A, B> {
    a: A,
    b: B,
}

#[derive(Debug)]
pub enum EitherError<A, B> {
    Left(A),
    Right(B),
    MultipleMutuallyExclusiveParams {
        left_name: String,
        right_name: String,
    },
}

impl<A: ParamError, B: ParamError> Display for EitherError<A, B> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            EitherError::Left(a) => fmt::Display::fmt(&a, f),
            EitherError::Right(b) => fmt::Display::fmt(&b, f),
            EitherError::MultipleMutuallyExclusiveParams {
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

impl<A: ParamError, B: ParamError> ParamError for EitherError<A, B> {}

impl<T, U, A, B> Param for Either<A, B>
where
    A: Param<Item = Option<T>>,
    B: Param<Item = Option<U>>,
{
    type Item = Option<either::Either<T, U>>;
    type Error = EitherError<A::Error, B::Error>;
    fn update_options(&self, opts: &mut getopts::Options) {
        self.a.update_options(opts);
        self.b.update_options(opts);
    }
    fn name(&self) -> String {
        format!("({} or {})", self.a.name(), self.b.name())
    }
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error> {
        let maybe_a = self.a.get(matches).map_err(EitherError::Left)?;
        let maybe_b = self.b.get(matches).map_err(EitherError::Right)?;
        match (maybe_a, maybe_b) {
            (Some(_), Some(_)) => Err(EitherError::MultipleMutuallyExclusiveParams {
                left_name: self.a.name(),
                right_name: self.b.name(),
            }),
            (Some(a), None) => Ok(Some(either::Left(a))),
            (None, Some(b)) => Ok(Some(either::Right(b))),
            (None, None) => Ok(None),
        }
    }
}

pub struct EitherHomogeneous<A, B> {
    a: A,
    b: B,
}

impl<T, A, B> Param for EitherHomogeneous<A, B>
where
    A: Param<Item = Option<T>>,
    B: Param<Item = Option<T>>,
{
    type Item = Option<T>;
    type Error = EitherError<A::Error, B::Error>;
    fn update_options(&self, opts: &mut getopts::Options) {
        self.a.update_options(opts);
        self.b.update_options(opts);
    }
    fn name(&self) -> String {
        format!("({} or {})", self.a.name(), self.b.name())
    }
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error> {
        let maybe_a = self.a.get(matches).map_err(EitherError::Left)?;
        let maybe_b = self.b.get(matches).map_err(EitherError::Right)?;
        match (maybe_a, maybe_b) {
            (Some(_), Some(_)) => Err(EitherError::MultipleMutuallyExclusiveParams {
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
    param: P,
    default: T,
}

impl<P, T> Param for WithDefault<P, T>
where
    T: Clone,
    P: Param<Item = Option<T>>,
{
    type Item = T;
    type Error = P::Error;
    fn update_options(&self, opts: &mut getopts::Options) {
        self.param.update_options(opts);
    }
    fn name(&self) -> String {
        self.param.name()
    }
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error> {
        Ok(self.param
            .get(matches)?
            .unwrap_or_else(|| self.default.clone()))
    }
}

pub struct Required<P> {
    param: P,
}

#[derive(Debug)]
pub enum RequiredError<E> {
    Other(E),
    MissingRequiredParam { name: String },
}

impl<E: ParamError> Display for RequiredError<E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            RequiredError::Other(e) => fmt::Display::fmt(&e, f),
            RequiredError::MissingRequiredParam { name } => {
                write!(f, "{} is required but not supplied", name)
            }
        }
    }
}

impl<E: ParamError> ParamError for RequiredError<E> {}

impl<P, T> Param for Required<P>
where
    P: Param<Item = Option<T>>,
{
    type Item = T;
    type Error = RequiredError<P::Error>;
    fn update_options(&self, opts: &mut getopts::Options) {
        self.param.update_options(opts);
    }
    fn name(&self) -> String {
        self.param.name()
    }
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error> {
        self.param
            .get(matches)
            .map_err(RequiredError::Other)?
            .ok_or(RequiredError::MissingRequiredParam {
                name: self.param.name(),
            })
    }
}

pub struct Convert<A, F> {
    param: A,
    f: F,
}

#[derive(Debug)]
pub enum ConvertError<O, T, E> {
    Other(O),
    ConversionFailed { name: String, error: E, value: T },
}

impl<O: ParamError, T: Debug + Display, E: Debug + Display> Display for ConvertError<O, T, E> {
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

impl<O: ParamError, T: Debug + Display, E: Debug + Display> ParamError for ConvertError<O, T, E> {}

impl<A, F, U, E> Param for Convert<A, F>
where
    A: Param,
    A::Item: Clone + Debug + Display,
    E: Debug + Display,
    F: Fn(A::Item) -> Result<U, E>,
{
    type Item = U;
    type Error = ConvertError<A::Error, A::Item, E>;
    fn update_options(&self, opts: &mut getopts::Options) {
        self.param.update_options(opts);
    }
    fn name(&self) -> String {
        self.param.name()
    }
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error> {
        self.param
            .get(matches)
            .map_err(ConvertError::Other)
            .and_then(|o| {
                (self.f)(o.clone()).map_err(|error| ConvertError::ConversionFailed {
                    name: self.param.name(),
                    value: o,
                    error,
                })
            })
    }
}

pub struct OptConvert<A, F> {
    param: A,
    f: F,
}

impl<T, A, U, F, E> Param for OptConvert<A, F>
where
    T: Clone + Debug + Display,
    E: Clone + Debug + Display,
    A: Param<Item = Option<T>>,
    F: Fn(T) -> Result<U, E>,
{
    type Item = Option<U>;
    type Error = ConvertError<A::Error, T, E>;
    fn update_options(&self, opts: &mut getopts::Options) {
        self.param.update_options(opts);
    }
    fn name(&self) -> String {
        self.param.name()
    }
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error> {
        self.param
            .get(matches)
            .map_err(ConvertError::Other)
            .and_then(|o| match o {
                Some(t) => (self.f)(t.clone()).map(Some).map_err(|error| {
                    ConvertError::ConversionFailed {
                        name: self.param.name(),
                        value: t,
                        error,
                    }
                }),
                None => Ok(None),
            })
    }
}

pub trait ParamExt: Param {
    fn map<U, F>(self, f: F) -> Map<Self, F>
    where
        F: Fn(Self::Item) -> U,
        Self: Sized,
    {
        Map { param: self, f }
    }
    fn try_map<U, E, F>(self, f: F) -> TryMap<Self, F>
    where
        E: Debug,
        F: Fn(Self::Item) -> Result<U, E>,
        Self: Sized,
    {
        TryMap { param: self, f }
    }
    fn join<B>(self, b: B) -> Join<Self, B>
    where
        B: Param,
        Self: Sized,
    {
        Join { a: self, b }
    }
    fn convert<F, U, E>(self, f: F) -> Convert<Self, F>
    where
        E: Debug + Display,
        F: Fn(Self::Item) -> Result<U, E>,
        Self: Sized,
        Self::Item: Clone + Debug,
    {
        Convert { param: self, f }
    }
}

impl<P: ?Sized> ParamExt for P
where
    P: Param,
{
}

pub trait ParamOptExt: Param + ParamExt {
    type OptItem;

    fn opt_map<U, F>(self, f: F) -> OptMap<Self, F>
    where
        F: Fn(Self::OptItem) -> U,
        Self: Sized,
    {
        OptMap { param: self, f }
    }

    fn opt_try_map<U, E, F>(self, f: F) -> OptTryMap<Self, F>
    where
        E: Debug,
        F: Fn(Self::OptItem) -> Result<U, E>,
        Self: Sized,
    {
        OptTryMap { param: self, f }
    }

    fn codepend<B>(self, b: B) -> Codepend<Self, B>
    where
        B: ParamOptExt,
        Self: Sized,
    {
        Codepend { a: self, b }
    }

    fn either<B>(self, b: B) -> Either<Self, B>
    where
        B: ParamOptExt,
        Self: Sized,
    {
        Either { a: self, b }
    }

    fn either_homogeneous<B>(self, b: B) -> EitherHomogeneous<Self, B>
    where
        B: ParamOptExt<OptItem = Self::OptItem>,
        Self: Sized,
    {
        EitherHomogeneous { a: self, b }
    }

    fn with_default(self, default: Self::OptItem) -> WithDefault<Self, Self::OptItem>
    where
        Self: Sized,
    {
        WithDefault {
            param: self,
            default,
        }
    }

    fn required(self) -> Required<Self>
    where
        Self: Sized,
    {
        Required { param: self }
    }

    fn opt_convert<F, U, E>(self, f: F) -> OptConvert<Self, F>
    where
        E: Debug + Display,
        F: Fn(Self::OptItem) -> Result<U, E>,
        Self: Sized,
        Self::OptItem: Clone + Debug,
    {
        OptConvert { param: self, f }
    }
}

impl<T, P: ?Sized> ParamOptExt for P
where
    P: Param<Item = Option<T>>,
{
    type OptItem = T;
}

pub trait ParamBoolExt: Param + ParamExt {
    fn some_if<T>(self, value: T) -> SomeIf<Self, T>
    where
        Self: Sized,
    {
        SomeIf { param: self, value }
    }
}

impl<P: ?Sized> ParamBoolExt for P
where
    P: Param<Item = bool>,
{
}

pub fn flag(short: &str, long: &str, doc: &str) -> impl Param<Item = bool> {
    Flag {
        short: short.to_string(),
        long: long.to_string(),
        doc: doc.to_string(),
    }
}

fn arg_opt_str(
    short: &str,
    long: &str,
    hint: &str,
    doc: &str,
) -> impl Param<Item = Option<String>> {
    Arg {
        short: short.to_string(),
        long: long.to_string(),
        hint: hint.to_string(),
        doc: doc.to_string(),
    }
}

pub fn arg_opt<T>(short: &str, long: &str, hint: &str, doc: &str) -> impl Param<Item = Option<T>>
where
    T: FromStr,
    <T as FromStr>::Err: Clone + Debug + Display,
{
    arg_opt_str(short, long, hint, doc).opt_convert(|s| s.parse())
}

pub fn arg_req<T>(short: &str, long: &str, hint: &str, doc: &str) -> impl Param<Item = T>
where
    T: FromStr,
    <T as FromStr>::Err: Clone + Debug + Display,
{
    arg_opt(short, long, hint, doc).required()
}

pub fn arg_opt_def<T>(
    short: &str,
    long: &str,
    hint: &str,
    doc: &str,
    default: T,
) -> impl Param<Item = T>
where
    T: Clone + FromStr,
    <T as FromStr>::Err: Clone + Debug + Display,
{
    arg_opt(short, long, hint, doc).with_default(default)
}

#[macro_export]
macro_rules! unflatten_closure {
    ( $p:pat => $tup:expr ) => {
        |$p| $tup
    };
    ( $p:pat => ( $($tup:tt)* ), $head:expr $(, $tail:expr)* ) => {
        unflatten_closure!( ($p, a) => ( $($tup)*, a) $(, $tail )* )
    };
}

#[macro_export]
macro_rules! join_params {
    ( $head:expr, $($tail:expr),* $(,)* ) => {{
        $head $( .join($tail) )*
            .map(
                unflatten_closure!(a => (a) $(, $tail )*)
            )
    }}
}

#[macro_export]
macro_rules! map_params {
    ( let { $($var:ident = $a:expr;)* } in { $b:expr } ) => {
        join_params! {
            $($a),*
        }.map(|($($var),*)| $b)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fmt::Write;

    fn string_fmt<D: Display>(d: &D) -> String {
        let mut s = String::new();
        write!(&mut s, "{}", d);
        s
    }

    #[test]
    fn example() {
        #[derive(Debug, Clone, PartialEq, Eq)]
        enum WindowSize {
            Dimensions { width: u32, height: u32 },
            FullScreen,
        }

        let dimensions = arg_opt("w", "width", "INT", "width")
            .codepend(arg_opt("e", "height", "INT", "height"))
            .opt_map(|(width, height)| WindowSize::Dimensions { width, height });

        let fullscreen = flag("f", "fullscreen", "fullscreen").some_if(WindowSize::FullScreen);

        let param = dimensions.either_homogeneous(fullscreen).required();

        match param.parse(&[""]) {
            Err(e) => assert_eq!(
                string_fmt(&e),
                "((width and height) or fullscreen) is required but not supplied"
            ),
            Ok(o) => panic!("{:?}", o),
        }

        match param.parse(&["--width", "potato"]) {
            Err(e) => assert_eq!(
                string_fmt(&e),
                "invalid value \"potato\" supplied for \"width\" (invalid digit found in string)"
            ),
            Ok(o) => panic!("{:?}", o),
        }

        match param.parse(&["--width", "4", "--height", "2", "--fullscreen"]) {
            Err(e) => assert_eq!(
                string_fmt(&e),
                "(width and height) and fullscreen are mutually exclusive but both were supplied"
            ),
            Ok(o) => panic!("{:?}", o),
        }

        match param.parse(&["--width", "4", "--fullscreen"]) {
            Err(e) => assert_eq!(
                string_fmt(&e),
                "width and height must be supplied together or not at all \
                 (width is supplied, height is missing)"
            ),
            Ok(o) => panic!("{:?}", o),
        }

        assert_eq!(
            param.parse(&["--fullscreen"]).unwrap(),
            WindowSize::FullScreen
        );

        assert_eq!(
            param.parse(&["--width", "4", "--height", "2"]).unwrap(),
            WindowSize::Dimensions {
                width: 4,
                height: 2,
            }
        );
    }

    #[derive(Debug, Clone, PartialEq, Eq)]
    struct Args {
        foo: String,
        bar: i64,
        baz: (bool, bool),
        qux: Option<u32>,
    }

    #[test]
    fn map_params() {
        let param = map_params! {
            let {
                foo = arg_req("f", "foo", "", "");
                bar = arg_req("b", "bar", "", "");
                baz = flag("l", "baz-left", "").join(flag("r", "baz-right", ""));
                qux = arg_opt("q", "qux", "", "");
            } in {
                Args { foo, bar, baz, qux }
            }
        };

        let args = param
            .parse(&[
                "--foo",
                "hello",
                "--bar",
                "12345",
                "--baz-right",
                "--qux",
                "42",
            ])
            .unwrap();

        assert_eq!(
            args,
            Args {
                foo: "hello".to_string(),
                bar: 12345,
                baz: (false, true),
                qux: Some(42),
            }
        );
    }

    #[test]
    fn join_params() {
        let baz = flag("l", "baz-left", "").join(flag("r", "baz-right", ""));
        let param = join_params! {
            arg_req("f", "foo", "", ""),
            arg_req("b", "bar", "", ""),
            baz,
            arg_opt("q", "qux", "", ""),
        }.map(|(foo, bar, baz, qux)| Args { foo, bar, baz, qux });

        let args = param
            .parse(&[
                "--foo",
                "hello",
                "--bar",
                "12345",
                "--baz-right",
                "--qux",
                "42",
            ])
            .unwrap();

        assert_eq!(
            args,
            Args {
                foo: "hello".to_string(),
                bar: 12345,
                baz: (false, true),
                qux: Some(42),
            }
        );
    }
}

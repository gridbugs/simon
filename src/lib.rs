extern crate either;
extern crate getopts;

use std::str::FromStr;
use std::fmt::Debug;
use std::ffi::OsStr;

#[derive(Debug)]
pub enum TopLevelError<E> {
    Getopts(getopts::Fail),
    Other(E),
}

impl<T> From<getopts::Fail> for TopLevelError<T> {
    fn from(f: getopts::Fail) -> Self {
        TopLevelError::Getopts(f)
    }
}

pub trait Param {
    type Item;
    type Error: Debug;
    fn update_options(&self, opts: &mut getopts::Options);
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error>;
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

impl<A, U, E, F> Param for TryMap<A, F>
where
    A: Param,
    E: Debug,
    F: Fn(A::Item) -> Result<U, E>,
{
    type Item = U;
    type Error = TryMapError<A::Error, E>;
    fn update_options(&self, opts: &mut getopts::Options) {
        self.param.update_options(opts);
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
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error> {
        self.param.get(matches).map(|v| v.map(&self.f))
    }
}

pub struct OptTryMap<A, F> {
    param: A,
    f: F,
}

#[derive(Debug)]
pub enum OptTryMapError<E, F> {
    Other(E),
    MapFailed(F),
}

impl<T, A, U, E, F> Param for OptTryMap<A, F>
where
    A: Param<Item = Option<T>>,
    E: Debug,
    F: Fn(T) -> Result<U, E>,
{
    type Item = Option<U>;
    type Error = OptTryMapError<A::Error, E>;
    fn update_options(&self, opts: &mut getopts::Options) {
        self.param.update_options(opts);
    }
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error> {
        self.param
            .get(matches)
            .map_err(OptTryMapError::Other)
            .and_then(|o| match o {
                Some(t) => (self.f)(t).map(Some).map_err(OptTryMapError::MapFailed),
                None => Ok(None),
            })
    }
}

pub struct Join<A, B> {
    a: A,
    b: B,
}

impl<A, B> Param for Join<A, B>
where
    A: Param,
    B: Param,
{
    type Item = (A::Item, B::Item);
    type Error = either::Either<A::Error, B::Error>;
    fn update_options(&self, opts: &mut getopts::Options) {
        self.a.update_options(opts);
        self.b.update_options(opts);
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
    MissingCodependantParam,
}

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
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error> {
        let maybe_a = self.a.get(matches).map_err(CodependError::Left)?;
        let maybe_b = self.b.get(matches).map_err(CodependError::Right)?;
        match (maybe_a, maybe_b) {
            (Some(a), Some(b)) => Ok(Some((a, b))),
            (None, None) => Ok(None),
            (Some(_), None) | (None, Some(_)) => Err(CodependError::MissingCodependantParam),
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
    MultipleMutuallyExclusiveParams,
}

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
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error> {
        let maybe_a = self.a.get(matches).map_err(EitherError::Left)?;
        let maybe_b = self.b.get(matches).map_err(EitherError::Right)?;
        match (maybe_a, maybe_b) {
            (Some(_), Some(_)) => Err(EitherError::MultipleMutuallyExclusiveParams),
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
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error> {
        let maybe_a = self.a.get(matches).map_err(EitherError::Left)?;
        let maybe_b = self.b.get(matches).map_err(EitherError::Right)?;
        match (maybe_a, maybe_b) {
            (Some(_), Some(_)) => Err(EitherError::MultipleMutuallyExclusiveParams),
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
    MissingRequiredParam,
    Other(E),
}

impl<P, T> Param for Required<P>
where
    P: Param<Item = Option<T>>,
{
    type Item = T;
    type Error = RequiredError<P::Error>;
    fn update_options(&self, opts: &mut getopts::Options) {
        self.param.update_options(opts);
    }
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error> {
        self.param
            .get(matches)
            .map_err(RequiredError::Other)?
            .ok_or(RequiredError::MissingRequiredParam)
    }
}

#[derive(Debug)]
pub enum ConvertError<T, E> {
    ConversionFailed { value: T },
    Other(E),
}

pub struct Convert<A, F> {
    param: A,
    f: F,
}

impl<A, F, U> Param for Convert<A, F>
where
    A: Param,
    A::Item: Clone + Debug,
    F: Fn(A::Item) -> Option<U>,
{
    type Item = U;
    type Error = ConvertError<A::Item, A::Error>;
    fn update_options(&self, opts: &mut getopts::Options) {
        self.param.update_options(opts);
    }
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error> {
        self.param
            .get(matches)
            .map_err(ConvertError::Other)
            .and_then(|o| (self.f)(o.clone()).ok_or(ConvertError::ConversionFailed { value: o }))
    }
}

pub struct OptConvert<A, F> {
    param: A,
    f: F,
}

impl<T, A, U, F> Param for OptConvert<A, F>
where
    T: Clone + Debug,
    A: Param<Item = Option<T>>,
    F: Fn(T) -> Option<U>,
{
    type Item = Option<U>;
    type Error = ConvertError<T, A::Error>;
    fn update_options(&self, opts: &mut getopts::Options) {
        self.param.update_options(opts);
    }
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error> {
        self.param
            .get(matches)
            .map_err(ConvertError::Other)
            .and_then(|o| match o {
                Some(t) => (self.f)(t.clone())
                    .map(Some)
                    .ok_or(ConvertError::ConversionFailed { value: t }),
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
    fn convert<F, U>(self, f: F) -> Convert<Self, F>
    where
        F: Fn(Self::Item) -> Option<U>,
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

    fn opt_convert<F, U>(self, f: F) -> OptConvert<Self, F>
    where
        F: Fn(Self::OptItem) -> Option<U>,
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

pub fn arg_opt<T: FromStr>(
    short: &str,
    long: &str,
    hint: &str,
    doc: &str,
) -> impl Param<Item = Option<T>> {
    arg_opt_str(short, long, hint, doc).opt_convert(|s| s.parse().ok())
}

pub fn arg_req<T: FromStr>(short: &str, long: &str, hint: &str, doc: &str) -> impl Param<Item = T> {
    arg_opt(short, long, hint, doc).required()
}

pub fn arg_opt_def<T: FromStr + Clone>(
    short: &str,
    long: &str,
    hint: &str,
    doc: &str,
    default: T,
) -> impl Param<Item = T> {
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn either_codepend_required() {
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
            Err(TopLevelError::Other(RequiredError::MissingRequiredParam)) => (),
            Ok(o) => panic!("{:?}", o),
            Err(e) => panic!("{:?}", e),
        }

        match param.parse(&["--width", "4", "--height", "2", "--fullscreen"]) {
            Err(TopLevelError::Other(RequiredError::Other(
                EitherError::MultipleMutuallyExclusiveParams,
            ))) => (),
            Ok(o) => panic!("{:?}", o),
            Err(e) => panic!("{:?}", e),
        }

        match param.parse(&["--width", "4", "--fullscreen"]) {
            Err(TopLevelError::Other(RequiredError::Other(EitherError::Left(
                CodependError::MissingCodependantParam,
            )))) => (),
            Ok(o) => panic!("{:?}", o),
            Err(e) => panic!("{:?}", e),
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

    #[test]
    fn multi_arg_program() {
        #[derive(Debug, Clone, PartialEq, Eq)]
        struct Args {
            foo: String,
            bar: i64,
            baz: (bool, bool),
            qux: Option<u32>,
        }

        let param = join_params! {
            arg_req("f", "foo", "", ""),
            arg_req("b", "bar", "", ""),
            flag("l", "baz-left", "").join(flag("r", "baz-right", "")),
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

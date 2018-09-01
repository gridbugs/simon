use either;
use getopts;
use param::*;

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

pub struct OptMap<A, F> {
    param: A,
    f: F,
}

impl<A, AOptional, U, F> Param for OptMap<A, F>
where
    A: Param<Item = Option<AOptional>>,
    F: Fn(AOptional) -> U,
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

pub struct OptJoin<A, B> {
    a: A,
    b: B,
}

#[derive(Debug)]
pub enum OptJoinError<A, B> {
    Left(A),
    Right(B),
    MissingCodependantParam,
}

impl<AOptional, BOptional, A, B> Param for OptJoin<A, B>
where
    A: Param<Item = Option<AOptional>>,
    B: Param<Item = Option<BOptional>>,
{
    type Item = Option<(AOptional, BOptional)>;
    type Error = OptJoinError<A::Error, B::Error>;
    fn update_options(&self, opts: &mut getopts::Options) {
        self.a.update_options(opts);
        self.b.update_options(opts);
    }
    fn get(&self, matches: &getopts::Matches) -> Result<Self::Item, Self::Error> {
        let maybe_a = self.a.get(matches).map_err(OptJoinError::Left)?;
        let maybe_b = self.b.get(matches).map_err(OptJoinError::Right)?;
        match (maybe_a, maybe_b) {
            (Some(a), Some(b)) => Ok(Some((a, b))),
            (None, None) => Ok(None),
            (Some(_), None) | (None, Some(_)) => Err(OptJoinError::MissingCodependantParam),
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

impl<AOptional, BOptional, A, B> Param for Either<A, B>
where
    A: Param<Item = Option<AOptional>>,
    B: Param<Item = Option<BOptional>>,
{
    type Item = Option<either::Either<AOptional, BOptional>>;
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

pub struct EitherSameType<A, B> {
    a: A,
    b: B,
}

impl<T, A, B> Param for EitherSameType<A, B>
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

pub trait ParamExt: Param {
    fn map<U, F>(self, f: F) -> Map<Self, F>
    where
        F: Fn(Self::Item) -> U,
        Self: Sized,
    {
        Map { param: self, f }
    }
    fn join<B>(self, b: B) -> Join<Self, B>
    where
        B: Param,
        Self: Sized,
    {
        Join { a: self, b }
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

    fn opt_join<B>(self, b: B) -> OptJoin<Self, B>
    where
        B: ParamOptExt,
        Self: Sized,
    {
        OptJoin { a: self, b }
    }

    fn either<B>(self, b: B) -> Either<Self, B>
    where
        B: ParamOptExt,
        Self: Sized,
    {
        Either { a: self, b }
    }

    fn either_same_type<B>(self, b: B) -> EitherSameType<Self, B>
    where
        B: ParamOptExt<OptItem = Self::OptItem>,
        Self: Sized,
    {
        EitherSameType { a: self, b }
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
}

impl<T, P: ?Sized> ParamOptExt for P
where
    P: Param<Item = Option<T>>,
{
    type OptItem = T;
}

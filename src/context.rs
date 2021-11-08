use std::{fmt::Debug, ops::Deref, sync::Arc};

use crate::containers::Symbol;

/// Represents the unique ID of a module.
#[derive(Copy, Clone, Eq, PartialEq, PartialOrd, Ord, Debug)]
pub struct ModuleId(pub Symbol);

/// Represents an input location.
#[derive(Copy, Clone, Eq, PartialEq, PartialOrd, Ord, Debug)]
pub struct CtxLocation {
    pub source: ModuleId,
    pub start_offset: usize,
    pub end_offset: usize,
}

/// Represents a reference-counted value that carries a context.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Ctx<T> {
    inner: Arc<T>,
    context: Option<CtxLocation>,
}

impl<T: Debug> Debug for Ctx<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.inner.fmt(f)
    }
}

impl<T> Ctx<T> {
    /// Obtains the context.
    pub fn ctx(&self) -> Option<CtxLocation> {
        self.context
    }
}

impl<T> Deref for Ctx<T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        self.inner.deref()
    }
}

impl<T> From<T> for Ctx<T> {
    fn from(val: T) -> Self {
        Ctx {
            inner: val.into(),
            context: None,
        }
    }
}

pub type CtxErr = Ctx<anyhow::Error>;

pub type CtxResult<T> = Result<T, CtxErr>;

pub trait ToCtxErr {
    type Okay;
    fn err_ctx(self, loc: Option<CtxLocation>) -> Result<Self::Okay, CtxErr>;
}

impl<T, E: Into<anyhow::Error>> ToCtxErr for Result<T, E> {
    type Okay = T;
    fn err_ctx(self, loc: Option<CtxLocation>) -> Result<Self::Okay, CtxErr> {
        self.map_err(|e| Ctx {
            inner: Arc::new(e.into()),
            context: loc,
        })
    }
}


pub trait ToCtx: Sized {
    fn with_ctx(self, loc: impl Into<Option<CtxLocation>>) -> Ctx<Self> {
        Ctx {
            inner: Arc::new(self),
            context: loc.into(),
        }
    }
}

impl<T: Sized> ToCtx for T {}
use std::{
    fmt::{Debug, Display},
    ops::Deref,
    path::Path,
    sync::{
        atomic::{AtomicUsize, Ordering},
        Arc,
    },
};

use dashmap::DashMap;
use internment::Intern;
use once_cell::sync::Lazy;

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

pub type CtxErr = Ctx<anyhow::Error>;

pub trait ToCtx: Sized {
    fn with_ctx(self, loc: impl Into<Option<CtxLocation>>) -> Ctx<Self> {
        Ctx {
            inner: Arc::new(self),
            context: loc.into(),
        }
    }
}

impl<T: Sized> ToCtx for T {}

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

/// Represents an input location.
#[derive(Copy, Clone, Eq, PartialEq, PartialOrd, Ord, Debug)]
pub struct CtxLocation {
    pub source: ModuleId,
    pub start_offset: usize,
    pub end_offset: usize,
}

/// Represents the unique ID of a module.
#[derive(Copy, Clone, Eq, PartialEq, PartialOrd, Ord, Debug, Hash)]
pub struct ModuleId {
    absolute_path: Intern<String>,
}

impl Display for ModuleId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(&self.absolute_path, f)
    }
}

impl ModuleId {
    /// Create a new one from a Path.
    pub fn from_path(path: &Path) -> Self {
        let canon = path.to_string_lossy().into_owned();
        ModuleId {
            absolute_path: Intern::new(canon),
        }
    }

    /// A module relative to this module.
    pub fn relative(self, frag: &str) -> Self {
        let mut path = Path::new(self.absolute_path.as_str()).to_owned();
        path.pop();
        path.push(frag);
        let new = path.to_string_lossy().into_owned();
        ModuleId {
            absolute_path: Intern::new(new),
        }
    }

    /// Load as file, fallibly.
    pub fn load_file(self) -> std::io::Result<String> {
        std::fs::read_to_string(self.absolute_path.as_str())
    }

    /// Returns a globally unique ID.
    pub fn uniqid(self) -> usize {
        static CACHE: Lazy<DashMap<ModuleId, usize>> = Lazy::new(DashMap::new);
        static GCOUNTER: AtomicUsize = AtomicUsize::new(0);
        *CACHE
            .entry(self)
            .or_insert_with(|| GCOUNTER.fetch_add(1, Ordering::Relaxed))
    }
}

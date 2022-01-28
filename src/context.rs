use colored::Colorize;
use std::{
    fmt::{Debug, Display},
    ops::{Deref, DerefMut},
    path::Path,
    sync::{
        atomic::{AtomicUsize, Ordering},
        Arc,
    },
};

use dashmap::DashMap;
use std::path::PathBuf;
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
#[derive(PartialEq, Eq, PartialOrd, Ord)]
pub struct Ctx<T> {
    inner: Arc<T>,
    context: Option<CtxLocation>,
}

impl<T> Clone for Ctx<T> {
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
            context: self.context.clone(),
        }
    }
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

impl<T: Clone> DerefMut for Ctx<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        Arc::make_mut(&mut self.inner)
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

impl<T: Display> Display for Ctx<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let error_location: String;
        let mut detailed_line: Option<String> = None;
        if let Some(ctx) = self.ctx() {
            if let Ok(source_full_string) =
                std::fs::read_to_string(Path::new(&ctx.source.to_string()))
            {
                let mut char_counter = 0;
                let mut errloc = ctx.source.to_string();
                for (lineno, line) in source_full_string.split('\n').enumerate() {
                    let line_len = line.len() + 1;
                    if char_counter + line.len() > ctx.start_offset {
                        let line_offset = ctx.start_offset - char_counter;
                        errloc = format!("{}:{}", ctx.source, lineno + 1);
                        detailed_line = Some(format!("{}\n{}", line, {
                            let mut toret = String::new();
                            for _ in 0..line_offset {
                                toret.push(' ');
                            }
                            toret.push_str(&format!("{}", "^".bright_green().bold()));
                            for _ in
                                1..(ctx.end_offset - ctx.start_offset).min(line.len() - line_offset)
                            {
                                toret.push_str(&format!("{}", "~".bright_green().bold()));
                            }
                            toret
                        }));
                        break;
                    }
                    char_counter += line_len
                }
                error_location = errloc;
            } else {
                error_location = ctx.source.to_string();
            }
        } else {
            error_location = "(unknown location)".to_string();
        }

        let err_str = format!(
            "{}: {} {}",
            error_location.bold(),
            "error:".bold().red(),
            self.inner.to_string().bold()
        );

        if let Some(line) = detailed_line {
            let lines = line.lines().collect::<Vec<&str>>().join("\n\t");
            std::fmt::Display::fmt(&format!("{}\n\t{}", err_str, lines), f)
        } else {
            std::fmt::Display::fmt(&err_str, f)
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
    /// Relative path from the project root directory
    absolute_path: Intern<String>,
}

impl Display for ModuleId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(&self.absolute_path, f)
    }
}

impl ModuleId {
    pub fn new(path: &Path) -> Self {
        // TODO make this some inner module representation so that it doesn't differ by OS
        let canon = path.to_string_lossy().into_owned();
        ModuleId {
            absolute_path: Intern::new(canon),
        }
    }

    /// Create a new one from a Path.
    pub fn from_path(path: &Path) -> Self {
        //println!("from path {:?}", path);
        //let canon = path.canonicalize().unwrap().to_string_lossy().into_owned();
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

/// Project root directory
#[derive(Clone)]
pub struct ProjectRoot(pub PathBuf);

impl ProjectRoot {
    /// Create a [ModuleId] relative to the root directory
    pub fn module_from_root(self, path: &Path) -> ModuleId {
        ModuleId::new(&self.0.join(path))
    }
}

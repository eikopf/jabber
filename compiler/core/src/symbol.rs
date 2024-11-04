//! Small wrapper over [`string_interner`].

use string_interner::{
    backend::{self, Backend},
    symbol,
};

const INTERNER_CAPACITY: usize = 256;

#[derive(Debug, Hash, Clone, Copy, PartialEq, Eq)]
pub struct Symbol(symbol::SymbolU32);

#[derive(Debug)]
pub struct StringInterner(backend::StringBackend<symbol::SymbolU32>);

impl StringInterner {
    pub fn new() -> Self {
        StringInterner(backend::StringBackend::with_capacity(INTERNER_CAPACITY))
    }

    pub fn intern(&mut self, s: &str) -> Symbol {
        let raw_symbol = self.0.intern(s);
        Symbol(raw_symbol)
    }

    pub fn intern_static(&mut self, s: &'static str) -> Symbol {
        let raw_symbol = self.0.intern_static(s);
        Symbol(raw_symbol)
    }

    pub fn resolve(&self, sym: Symbol) -> Option<&str> {
        self.0.resolve(sym.0)
    }
}

impl Default for StringInterner {
    fn default() -> Self {
        Self::new()
    }
}

//! Small wrapper over [`string_interner`].

use string_interner::{self, backend, symbol};

/// The initial capcity of a [`StringInterner`].
///
/// At time of writing, [`string_interner`] will multiply this value by 5 and
/// pass it to [`String::with_capacity`]. This is based on the assumption that
/// the typical word size is 5 characters.
const INTERNER_CAPACITY: usize = 1024;

#[derive(Debug, Hash, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Symbol(symbol::SymbolU32);

#[derive(Debug)]
pub struct StringInterner(
    string_interner::StringInterner<backend::StringBackend<symbol::SymbolU32>>,
);

impl StringInterner {
    pub fn new() -> Self {
        StringInterner(string_interner::StringInterner::with_capacity(
            INTERNER_CAPACITY,
        ))
    }

    pub fn intern(&mut self, s: &str) -> Symbol {
        let raw_symbol = self.0.get_or_intern(s);
        Symbol(raw_symbol)
    }

    pub fn intern_static(&mut self, s: &'static str) -> Symbol {
        let raw_symbol = self.0.get_or_intern_static(s);
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

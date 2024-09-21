//! Concrete syntax tree types

#[derive(Debug, Clone)]
pub enum Ty {
    Never,
    Unit,
    Bool,
    Char,
    String,
    F32,
    F64,
    Int(Signedness, IntWidth),
    Tuple(Box<(Self, Self)>, Box<[Self]>),
    Fn(Box<(Self, Self)>),
    Named(Name, Box<[Self]>),
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Signedness {
    Unsigned,
    Signed,
}

impl Signedness {
    pub const fn to_prefix(self) -> &'static str {
        match self {
            Signedness::Unsigned => "u",
            Signedness::Signed => "i",
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum IntWidth {
    One,
    Two,
    Four,
    Eight,
    Ptr,
}

impl IntWidth {
    pub const fn to_suffix(self) -> &'static str {
        match self {
            IntWidth::One => "8",
            IntWidth::Two => "16",
            IntWidth::Four => "32",
            IntWidth::Eight => "64",
            IntWidth::Ptr => "size",
        }
    }
}

pub type Ident = Box<str>;
pub type Name = Box<(Box<[Ident]>, Ident)>;

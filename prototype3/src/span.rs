#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct Spanned<T, O = u32> {
    pub value: T,
    pub span: Span<O>,
}

pub type Span<O = u32> = (O, O);

//! Code generation.

use pretty::RcDoc;
use recursion::CollapsibleExt;

use crate::{
    package::metadata::PackageKind,
    symbol::{StringInterner, Symbol},
};

pub mod blame;
pub mod lower;
pub mod repr;
pub mod scm;

pub trait ToDoc {
    fn to_doc(self, interner: &mut StringInterner) -> RcDoc<'static, ()>;
}

impl ToDoc for Symbol {
    fn to_doc(self, interner: &mut StringInterner) -> RcDoc<'static, ()> {
        let str = interner.resolve(self).unwrap();
        RcDoc::as_string(str)
    }
}

impl ToDoc for scm::Literal {
    fn to_doc(self, interner: &mut StringInterner) -> RcDoc<'static, ()> {
        self.to_opt_doc(interner).unwrap()
    }
}

impl ToDoc for scm::Pattern {
    fn to_doc(self, interner: &mut StringInterner) -> RcDoc<'static, ()> {
        self.collapse_frames(|frame| frame.to_opt_doc(interner).unwrap())
    }
}

impl ToDoc for scm::Expr {
    fn to_doc(self, interner: &mut StringInterner) -> RcDoc<'static, ()> {
        self.collapse_frames(|frame| frame.to_opt_doc(interner).unwrap())
    }
}

impl<T: ToDoc> ToDoc for blame::Blamed<T> {
    fn to_doc(self, interner: &mut StringInterner) -> RcDoc<'static, ()> {
        self.item.to_doc(interner)
    }
}

impl<T: ToDoc> ToDoc for lower::Def<T> {
    fn to_doc(self, interner: &mut StringInterner) -> RcDoc<'static, ()> {
        let name = RcDoc::as_string(interner.resolve(self.name.item).unwrap());
        let value = self.value.to_doc(interner);

        RcDoc::text("(")
            .append(RcDoc::text("define"))
            .append(RcDoc::space())
            .append(name)
            .append(RcDoc::softline())
            .append(value)
            .append(RcDoc::text(")"))
    }
}

impl ToDoc for lower::LoweredPackage {
    fn to_doc(self, interner: &mut StringInterner) -> RcDoc<'static, ()> {
        // if this is a binary package, replace any possible exports with the
        // singular export `<name>/main`.
        let exports = match self.kind {
            PackageKind::Binary => {
                let root = interner.resolve(self.name).unwrap();
                let main = interner.intern(&format!("{root}/main"));
                vec![main]
            }
            PackageKind::Library => self.exports,
        }
        .into_iter()
        .map(|e| e.to_doc(interner));

        let exports = RcDoc::text("(")
            .append(RcDoc::text("export"))
            .append(RcDoc::line())
            .append(RcDoc::intersperse(exports, RcDoc::line()).nest(2))
            .append(")");

        let imports = RcDoc::text("(")
            .append("import")
            .append(RcDoc::softline())
            .append(RcDoc::text("(support support)").nest(2))
            .append(RcDoc::softline_())
            .append(
                RcDoc::intersperse(
                    self.imports.into_iter().map(|i| {
                        RcDoc::text("(target")
                            .append(RcDoc::softline())
                            .append(i.to_doc(interner))
                            .append(")")
                    }),
                    RcDoc::softline_(),
                )
                .nest(2),
            )
            .append(")");

        let externals = self
            .externals
            .into_iter()
            .map(|ext| ext.to_doc(interner))
            .collect::<Vec<_>>();

        let constrs = self
            .constrs
            .into_iter()
            .map(|ext| ext.to_doc(interner))
            .collect::<Vec<_>>();

        let functions = self
            .functions
            .into_iter()
            .map(|ext| ext.to_doc(interner))
            .collect::<Vec<_>>();

        let constants = self
            .constants
            .into_iter()
            .map(|ext| ext.to_doc(interner))
            .collect::<Vec<_>>();

        RcDoc::text("(")
            .append(RcDoc::text("library"))
            .append(RcDoc::space())
            .append(RcDoc::text("("))
            .append(RcDoc::as_string(interner.resolve(self.name).unwrap()))
            .append(RcDoc::text(")"))
            .append(RcDoc::line().nest(2))
            .append(exports)
            .append(RcDoc::line_())
            .append(imports)
            .append(RcDoc::line_())
            .append(RcDoc::intersperse(externals, RcDoc::line()).nest(2))
            .append(RcDoc::line_())
            .append(RcDoc::intersperse(constrs, RcDoc::line()).nest(2))
            .append(RcDoc::line_())
            .append(RcDoc::intersperse(functions, RcDoc::line()).nest(2))
            .append(RcDoc::line_())
            .append(RcDoc::intersperse(constants, RcDoc::line()).nest(2))
            .append(RcDoc::line_())
            .append(RcDoc::text(")").nest(2))
    }
}

//! Unbound environments that precede import and name resolution.

use crate::{
    ast::{
        common::{ViSp, Vis},
        unbound_lowered as ubd,
    },
    package as pkg,
    span::Spanned,
    symbol::Symbol,
};

use super::{Env, ModId, TermId, TypeId};

/// A completely unresolved environment.
pub type UnboundEnv =
    Env<Spanned<ubd::Term>, Spanned<ubd::Type>, UnboundModItems>;

#[derive(Debug, Clone, Default)]
pub struct UnboundModItems {
    pub imports: Vec<ViSp<ubd::Import>>,
    pub submodules: Vec<ViSp<ModId>>,
    pub terms: Vec<ViSp<TermId>>,
    pub types: Vec<ViSp<TypeId>>,
}

impl UnboundEnv {
    pub fn consume_package(
        &mut self,
        pkg::Package {
            name,
            version,
            root_module,
            ..
        }: pkg::Package<ubd::Ast>,
        dependencies: Box<[Symbol]>,
    ) -> Symbol {
        // register root file and package
        let root_file = self.register_file(root_module.content.file.clone());
        let package = self.register_package(
            name.as_ref(),
            version,
            root_file,
            dependencies,
        );

        // recursively populate table using module tree
        let root_module_id = self.get_package(package).root_module;
        self.populate_module(root_module, root_module_id, package);

        // return package id
        package
    }

    pub fn populate_module(
        &mut self,
        pkg::Module {
            content,
            submodules,
            ..
        }: pkg::Module<ubd::Ast>,
        mod_id: ModId,
        package: Symbol,
    ) {
        for module in submodules {
            // register file
            let file = self.register_file(module.content.file.clone());
            // register empty submodule
            let id = self.register_module(
                module.name.as_ref(),
                Some(mod_id),
                file,
                package,
            );
            // populate submodule
            self.populate_module(module, id, package);
        }

        let ubd::Ast {
            imports,
            terms,
            types,
            ..
        } = content;

        for import in imports {
            self.insert_import(import, mod_id);
        }

        for term in terms {
            self.insert_term(term, mod_id);
        }

        for ty in types {
            self.insert_type(ty, mod_id);
        }
    }

    pub fn insert_import(&mut self, import: ViSp<ubd::Import>, module: ModId) {
        let module = self.get_module_mut(module);
        module.items.imports.push(import);
    }

    pub fn insert_term(
        &mut self,
        Vis {
            visibility,
            item: Spanned { item, span },
        }: ViSp<ubd::Term>,
        module: ModId,
    ) {
        // get name in source
        let file = self.get_file(self.get_module(module).file);
        let name = item.name(file.contents().as_bytes());

        // register term in env table
        let term = self.register_term(name, module, span.with(item));

        // insert term into module
        let module = self.get_module_mut(module);
        module.items.terms.push(visibility.with(span.with(term)));
    }

    pub fn insert_type(
        &mut self,
        Vis {
            visibility,
            item: Spanned { item, span },
        }: ViSp<ubd::Type>,
        module: ModId,
    ) {
        // get name in source
        let file = self.get_file(self.get_module(module).file);
        let name = item.name(file.contents().as_bytes());

        // register type in env table
        let ty = self.register_type(name, module, span.with(item));

        // insert type into module
        let module = self.get_module_mut(module);
        module.items.types.push(visibility.with(span.with(ty)));
    }
}

#[cfg(test)]
mod tests {
    use std::{path::PathBuf, str::FromStr};

    use crate::cst::Parser;

    use super::*;

    #[test]
    fn build_unbound_env_from_core() {
        let path = PathBuf::from_str("../../libs/core").unwrap();
        let package = pkg::Package::load_files(path).unwrap();
        let mut parser = Parser::new().unwrap();

        let package = package
            .map_modules(|file| parser.parse(file))
            .transpose()
            .unwrap()
            .map_modules(crate::ast::unbound::Ast::try_from)
            .transpose()
            .unwrap()
            .map_modules(crate::ast::unbound_lowered::Ast::from);

        let mut env = UnboundEnv::new();
        let core_symbol = env.consume_package(package, Box::new([]));

        //dbg!(&env);

        for module in &env.modules {
            eprintln!("MOD: {}", env.interner.resolve(module.name).unwrap());
        }

        eprintln!("PKG: {}", env.interner.resolve(core_symbol).unwrap());

        //dbg!(&env.modules);
        //dbg!(&env.modules[7].imports);
        dbg!(&env.packages);

        panic!();
    }
}

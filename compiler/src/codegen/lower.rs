//! Primary lowering implementation.

use std::collections::HashMap;

use crate::{
    env::{FileId, ModId, typed::TypedEnv},
    symbol::Symbol,
};

use super::{
    blame::Blamed,
    repr::{MonoTyId, Shape},
    scm::Module,
};

#[derive(Debug, Clone)]
pub struct LoweredPackage {
    pub name: Symbol,
    pub root_file: FileId,
    pub root_module: Module,
}

#[derive(Debug)]
pub struct Lowerer<'a> {
    /// The typechecked environment.
    env: &'a mut TypedEnv,
    /// Lowered monotype representations.
    type_reprs: HashMap<MonoTyId, Shape>,
    /// The next unused monotype ID.
    next_mono_ty_id: MonoTyId,
}

impl<'a> Lowerer<'a> {
    pub fn new(env: &'a mut TypedEnv) -> Self {
        Self {
            env,
            type_reprs: Default::default(),
            next_mono_ty_id: MonoTyId::MIN,
        }
    }

    pub fn lower_package(&mut self, package: Symbol) -> LoweredPackage {
        todo!()
    }

    pub fn lower_module(&mut self, module: ModId) -> Blamed<Module> {
        todo!()
    }

    /// Returns an unused monotype ID.
    pub fn fresh_mono_ty_id(&mut self) -> MonoTyId {
        let id = self.next_mono_ty_id;
        self.next_mono_ty_id.increment();
        id
    }
}

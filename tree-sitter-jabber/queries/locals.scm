;; REFERENCES

(ident) @local.reference

;; DEFINITIONS

;; mod decls
(mod_decl name: (ident) @local.definition)

;; use decls
(use_decl (ident) @local.definition)
(use_decl (path name: (ident) @local.definition))

(alias_item alias: (ident) @local.definition)
(tree_item (ident) @local.definition)

;; functions
(fn_decl name: (ident) @local.definition)
(extern_fn_decl name: (ident) @local.definition)

;; variables
(parameter pattern: (ident) @local.definition)

;; types
(struct_decl name: (ident) @local.definition)
(enum_decl   name: (ident) @local.definition)

(struct_field name: (ident) @local.definition)
(enum_variant name: (ident) @local.definition)

(type_decl        name: (ident) @local.definition)
(extern_type_decl name: (ident) @local.definition)

(generic_params (ident) @local.definition)

;; SCOPES

[
 (block)
 (fn_decl)
 (if_else_expr)
 (match_expr)
 (match_arm)
 (struct_decl)
 (enum_decl)
 ] @local.scope


open Sexplib
open Sexplib.Std

(** An atomic identifier. *)
type ident = Ident of string
[@@deriving (eq, show, sexp)]

(** A possibly-qualified name, consisting of 
    a prefix sequence and terminal identifier. *)
type name = Name of (ident list) * ident
[@@deriving (eq, show)]

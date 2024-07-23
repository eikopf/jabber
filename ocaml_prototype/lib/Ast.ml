open Sexplib
open Sexplib.Std (* required import for the sexp macro *)

(** An atomic identifier. *)
type ident = Ident of string
[@@deriving (eq, show, sexp)]

let ident_to_string = function
  | Ident x -> x

(** A possibly-qualified identifier, consisting of 
    a prefix sequence of identifiers and a terminal 
    identifier. *)
type name = Name of (ident list) * ident
[@@deriving (eq, show, sexp)]

let name_to_string = function
  | Name ([], Ident (suffix)) -> suffix
  | Name (prefix, Ident (suffix)) -> 
      (String.concat "::" (List.map ident_to_string prefix)) ^ "::" ^ suffix

type sign =
  | Unsigned
  | Signed
[@@deriving (eq, show, sexp)]

let sign_to_string = function
  | Unsigned -> "u"
  | Signed   -> "i"

type int_width =
  | W8
  | W16
  | W32
  | W64
  | WPtr
[@@deriving (eq, show, sexp)]

let width_to_string = function
  | W8   -> "8"
  | W16  -> "16"
  | W32  -> "32"
  | W64  -> "64"
  | WPtr -> "size"

(** A structured type. *)
type ty =
  | BottomTy      
  (** The canonical uninhabited type, denoted [!]. *)
  | UnitTy
  (** The canonical singleton type, denoted [()].*)
  | BoolTy
  (** The canonical binary type, denoted [bool].*)
  | CharTy
  (** The character type, denoted [char]. *)
  | StringTy
  (** The string type, denoted [string]. *)
  | F32Ty
  (** The single-precision IEEE floating-point type, denoted [f32].*)
  | F64Ty
  (** The double-precision IEEE floating-point type, denoted [f64].*)
  | IntTy of sign * int_width
  (** An integer type consisting of a sign prefix and width suffix. *)
  | TupleTy of ty * ty * (ty list)
  (** A tuple type composed from at least 2 types. *)
  | FuncTy of ty * ty
  (** A function type consisting of a domain and codomain,
      and written using the [->] operator. *)
  | NameTy of name * (ty list)
  (** A named type with optional type arguments. *)
[@@deriving (show, sexp)]

let rec type_to_string = function
  | BottomTy -> "!"
  | UnitTy   -> "()"
  | BoolTy   -> "bool"
  | CharTy   -> "char"
  | StringTy -> "string"
  | F32Ty    -> "f32"
  | F64Ty    -> "f64"
  | IntTy   (s,     w) -> 
      (sign_to_string s) ^ (width_to_string w)
  | FuncTy  (l,     r) -> 
      (type_to_string l) ^ " -> " ^ (type_to_string r)
  | NameTy  (n,    ts) -> 
      (name_to_string n) ^ "[" ^ (String.concat ", " (List.map type_to_string ts)) ^ "]"
  | TupleTy (t, u, vs) -> 
      String.concat ", " (List.map type_to_string (t :: u :: vs))

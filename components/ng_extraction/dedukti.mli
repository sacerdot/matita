(** Syntax of Dedukti **)

type comment = string
type var = string
type constname = string
type pragma = string

type modname = string
(** Names of modules **)

type const = modname * constname
(** Constants are qualified by the name of the module in which they are defined. **)

type sort = Type | Kind

type term =
  | Var of var
  | Const of const
  | Sort of sort
  | Prod of var * term * term
  | Lam of var * term * term
  | App of term * term

val prods : (var * term) list -> term -> term
(** Shortcuts for n-ary term constructors **)

val lams : (var * term) list -> term -> term
val apps : term -> term list -> term
val app_bindings : term -> (var * term) list -> term

(** Left-hand side of rewrite rules **)
type pattern =
  | PVar of var
  | PConst of const
  | PLam of var * pattern * pattern
  | PApp of pattern * pattern
  | PGuard of term

val plams : (var * term) list -> pattern -> pattern
(** Shortcuts for n-ary term constructors **)

val papps : pattern -> pattern list -> pattern
val papp_bindings : pattern -> (var * term) list -> pattern

type context = (var * term) list
(** Context of rewrite rules
    WARNING: Contexts are stored in reverse order. **)

val app_context : term -> context -> term
(** Shortcut for applying a term to the variables of a context **)

val papp_context : pattern -> context -> pattern

(** Commands such as module name declaration, evaluation, ... **)
type command = Require of modname

type entry =
  | StcDeclaration of constname * term
  | DefDeclaration of constname * term
  | Definition of constname * term option * term
  | RewriteRule of context * pattern * term
  | Command of command
  | Comment of comment
  | Pragma of pragma

type signature = entry list
(** Content of a dedukti file
    WARNING: Signatures are stored in reverse order. **)

val dk_keywords : string list

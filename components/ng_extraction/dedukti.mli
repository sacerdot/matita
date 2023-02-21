(** Syntax of Dedukti **)

type comment = string

type var = string

type constname = string

(** Names of modules **)
type modname = string

(** Constants are qualified by the name of the module in which they are defined. **)
type const = modname * constname

type sort = Type | Kind

type term =
| Var   of var
| Const of const
| Sort  of sort
| Prod  of var * term * term
| Lam   of var * term * term
| App   of term * term

(** Shortcuts for n-ary term constructors **)
val prods : (var * term) list -> term -> term
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

(** Shortcuts for n-ary term constructors **)
val plams : (var * term) list -> pattern -> pattern
val papps : pattern -> pattern list -> pattern
val papp_bindings : pattern -> (var * term) list -> pattern

(** Context of rewrite rules
    WARNING: Contexts are stored in reverse order. **)
type context = (var * term) list

(** Shortcut for applying a term to the variables of a context **)
val app_context : term -> context -> term
val papp_context : pattern -> context -> pattern

(** Commands such as module name declaration, evaluation, ... **)
type command =
| Require of modname

type entry =
| StcDeclaration of constname * term
| DefDeclaration of constname * term
| Definition of constname * term option * term
| RewriteRule of context * pattern * term
| Command of command
| Comment of comment

(** Content of a dedukti file
    WARNING: Signatures are stored in reverse order. **)
type signature = entry list

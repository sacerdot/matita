(*                     name     recno body-name*)
type fp_pragma_attrs = string * int * string

(*                      name     cons name *)
type ind_pragma_attrs = string * string list

type export_pragma = 
  | GeneratedPragma
  (*                  type                   body                    attrs *)
  | FixpointPragma of (Parsers.Entry.entry * Parsers.Entry.entry * fp_pragma_attrs) list
  (*                   leftno  type                  constructors               attrs                   match const entry *)
  | InductivePragma of int * (Parsers.Entry.entry * Parsers.Entry.entry list * ind_pragma_attrs) list * Parsers.Entry.entry option(*TODO*)


val pragma_name: string -> string

val parse_block: string -> string -> Parsers.Entry.entry list -> export_pragma option

val is_valid_export_pragma: string -> bool


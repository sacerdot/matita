(*                     name     recno body-name*)
type fp_pragma_attrs = string * int * string

(*                      name     cons name *)
type ind_pragma_attrs = string * string list

type export_pragma = 
  | GeneratedPragma
  (*                  type                   body                    attrs *)
  | FixpointPragma of (Parsers.Entry.entry * Parsers.Entry.entry * fp_pragma_attrs) list
  (*                  leftno  type                  constructors               attrs *)
  | InductivePragma of int * (Parsers.Entry.entry * Parsers.Entry.entry list * ind_pragma_attrs) list


val parse_block: string -> Parsers.Parser.stream -> export_pragma option


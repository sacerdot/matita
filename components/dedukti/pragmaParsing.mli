(*                     name     recno body-name*)
type fp_pragma_attrs = string * int * string

type export_pragma = 
  | GeneratedPragma
  (*                  type                   body                    attrs *)
  | FixpointPragma of (Parsers.Entry.entry * Parsers.Entry.entry * fp_pragma_attrs) list
  (*                  leftno *)
  | InductivePragma of int

val parse_block: string -> Parsers.Parser.stream -> export_pragma option


type export_pragma_values

val mk_pragma_val: string -> string -> export_pragma_values
val pragma_begin: export_pragma_values -> string
val pragma_end: export_pragma_values -> string

type export_pragma = 
  | GeneratedPragma of export_pragma_values 
  | FixpointPragma of export_pragma_values * Parsers.Entry.entry * Parsers.Entry.entry

val parse_pragma: string -> Parsers.Parser.stream -> export_pragma option


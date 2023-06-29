
type export_pragma = 
  (*                  begin/end values *)
  | GeneratedPragma 
  (*                  begin/end values       type                  body                  recno *)
  | FixpointPragma of  Parsers.Entry.entry * Parsers.Entry.entry * int
  (*                  begin/end values      leftno *)
      | InductivePragma of  int

val parse_pragma: string -> Parsers.Parser.stream -> export_pragma option


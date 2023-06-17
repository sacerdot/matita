(* TODO *)
val eval_from_dedukti_stream: asserted:'a -> baseuri:string -> (#GrafiteTypes.status as 'b)-> Parsers.Parser.stream -> 'a * 'b
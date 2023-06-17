(* Pragmas *)
type export_pragma_values = string * string
let mk_pragma_val b e = (b, e)
let pragma_begin (b, _) = b
let pragma_end (_, e) = e

type export_pragma = 
  | GeneratedPragma of export_pragma_values 
  | FixpointPragma of export_pragma_values * Parsers.Entry.entry * Parsers.Entry.entry

let generated_pragma = mk_pragma_val "PRAGMA BEGIN GENERATED" "PRAGMA END GENERATED"
let fixpoint_pragma = mk_pragma_val "PRAGMA BEGIN FIXPOINT" "PRAGMA END FIXPOINT"

let rec skip_until_end_of_pragma pragma buf = 
  let entry = Parsers.Parser.read buf in
  match entry with 
  | Parsers.Entry.Pragma(_, str) when str = (pragma_end pragma) -> None
  | _ -> skip_until_end_of_pragma pragma buf

let parse_generate_pragma buf = 
  let _ = skip_until_end_of_pragma generated_pragma buf in 
  Some (GeneratedPragma generated_pragma)

let parse_fixpoint_pragma buf =
  let type_def = Parsers.Parser.read buf in
  let _ = Parsers.Parser.read buf in 
  let _ = Parsers.Parser.read buf in 
  let rule_body = Parsers.Parser.read buf in
  let pragmaend = Parsers.Parser.read buf in
  match type_def, rule_body, pragmaend with
  | Parsers.Entry.Decl (_,_,_,_,_), Parsers.Entry.Rules(_,_), Parsers.Entry.Pragma(_, _) -> 
    Some (FixpointPragma (fixpoint_pragma, type_def, rule_body))
  | _ ->  
    HLog.error("Error parsing malformed fixpoint"); 
    None


let parse_pragma pragma_str buf = 
  match pragma_str with   
  | s when s = pragma_begin generated_pragma -> parse_generate_pragma buf
  | s when s = pragma_begin fixpoint_pragma -> parse_fixpoint_pragma buf
  | _ -> HLog.message("Found uknown pragma '" ^ pragma_str ^ "'");
    None


(* Pragmas *)
type export_pragma_values = string * string
let mk_pragma_val b e = (b, e)
let pragma_begin (b, _) = b
let pragma_end (_, e) = e

type export_pragma = 
  | GeneratedPragma of export_pragma_values 
  (*                  begin/end values       type                  body                  recno *)
  | FixpointPragma of export_pragma_values * Parsers.Entry.entry * Parsers.Entry.entry * int

let generated_pragma = mk_pragma_val "PRAGMA BEGIN GENERATED" "PRAGMA END GENERATED"
let fixpoint_pragma = mk_pragma_val "PRAGMA BEGIN FIXPOINT" "PRAGMA END FIXPOINT"
let recno_attr = "RECNO"

(* UTILS *)
let find_index_opt str substr =
  try
    let regex = Str.regexp substr in
    let match_start = Str.search_forward regex str 0 in
    Some match_start
  with Not_found -> None

let get_attr pragma_str attr =
  let pattern = attr ^ "=" in
  let attr_index = find_index_opt pragma_str pattern in
  match attr_index with
  | Some index ->
    let start_index = index + String.length pattern in
    let attr_str = String.sub pragma_str start_index (String.length pragma_str - start_index) in
    Some attr_str
  | None -> None

let bounded_equal l1 l2 b =
  let rec aux l1 l2 b index =
    if index < b then
      try 
        List.nth l1 index = List.nth l2 index && aux l1 l2 b (index + 1)
      with _ -> false
    else 
      true
  in
aux l1 l2 b 0

let same_type pragma_1 pragma_2 =
  let p1 = String.split_on_char ' ' pragma_1 in
  let p2 = String.split_on_char ' ' pragma_2 in
  (* Just check the first three words: eg PRAGMA BEGIN NAME*)
  bounded_equal p1 p2 3


let rec skip_until_end_of_pragma pragma buf = 
  let entry = Parsers.Parser.read buf in
  match entry with 
  | Parsers.Entry.Pragma(_, str) when str = (pragma_end pragma) -> None
  | _ -> skip_until_end_of_pragma pragma buf

let parse_generate_pragma buf = 
  let _ = skip_until_end_of_pragma generated_pragma buf in 
  Some (GeneratedPragma generated_pragma)

let parse_fixpoint_pragma buf pragma_str =
  let type_def = Parsers.Parser.read buf in
  let _ = Parsers.Parser.read buf in 
  let _ = Parsers.Parser.read buf in 
  let rule_body = Parsers.Parser.read buf in
  let pragmaend = Parsers.Parser.read buf in
  match type_def, rule_body, pragmaend with
  | Parsers.Entry.Decl (_,_,_,_,_), Parsers.Entry.Rules(_,_), Parsers.Entry.Pragma(_, _) -> (
    let recno_opt = get_attr pragma_str recno_attr in
    match recno_opt with
    | Some str -> Some (FixpointPragma (fixpoint_pragma, type_def, rule_body, (int_of_string str)))
    | None -> 
      HLog.error ("Malformed fixpoint pragma: missing 'recno' attribute in pragma '" ^ pragma_str ^ "' ");
      None
    )
  | _ ->  
    HLog.error ("Malformed fixpoint pragma: error in parsing content of pragma '" ^ pragma_str ^ "'"); 
    None


let parse_pragma pragma_str buf = 
  match pragma_str with   
  | s when same_type s (pragma_begin generated_pragma) -> parse_generate_pragma buf
  | s when same_type s  (pragma_begin fixpoint_pragma) -> parse_fixpoint_pragma buf pragma_str
  | _ -> HLog.message("Found uknown pragma '" ^ pragma_str ^ "'");
    None


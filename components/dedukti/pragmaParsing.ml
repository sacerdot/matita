type export_pragma = 
  | GeneratedPragma
  (*                  type                  body                  recno *)
  | FixpointPragma of Parsers.Entry.entry * Parsers.Entry.entry * int
  (*                  leftno *)
  | InductivePragma of int

let generated_pragma = "GENERATED"
let fixpoint_pragma = "FIXPOINT"
let inductive_pragma = "INDUCTIVE"
let recno_attr = "RECNO"
let leftno_attr = "LEFTNO"

(* Given a string of type 'PRAGMA <BEGIN/GENERATED> <NAME> [ATTR=...]' returns the `NAME` part *)
let pragma_name pragma_str = 
  try 
    let splitted = String.split_on_char ' ' pragma_str in 
    Some (List.nth splitted 2)
  with _ -> None

let missing_attr pragma_str attr pragma_type =
  HLog.error ("Malformed " ^ pragma_type ^ " pragma: missing '" ^ attr ^ "' attribute in pragma '" ^ pragma_str ^ "' ");
  None


let find_index_opt str substr =
  try
    let regex = Str.regexp substr in
    let match_start = Str.search_forward regex str 0 in
    Some match_start
  with Not_found -> None

(* TODO fix for multiple args *)
let get_attr pragma_str attr =
  let pattern = attr ^ "=" in
  let attr_index = find_index_opt pragma_str pattern in
  match attr_index with
  | Some index ->
    let start_index = index + String.length pattern in
    let splitted = String.split_on_char ' ' (String.sub pragma_str start_index (String.length pragma_str - start_index)) in
    Some (List.nth splitted 0)
  | None -> None

let bound_equal l1 l2 b =
  let rec aux l1 l2 b =
   match l1,l2 with
   | _,_ when b=0 -> true
   | hd1::tl1,hd2::tl2 -> hd1=hd2 && aux tl1 tl2 (b-1)
   | _,_ -> false in
   aux l1 l2 b

let same_type pragma_1 pragma_2 =
  let p1 = String.split_on_char ' ' pragma_1 in
  let p2 = String.split_on_char ' ' pragma_2 in
  (* Just check the first three words: eg PRAGMA BEGIN NAME*)
  bound_equal p1 p2 3

let rec skip_until_end_of_pragma pragma buf = 
  let entry = Parsers.Parser.read buf in
  match entry with 
  | Parsers.Entry.Pragma(_, str) when str = pragma -> ()
  | _ -> skip_until_end_of_pragma pragma buf

let parse_generated_pragma buf = 
  let _ = skip_until_end_of_pragma generated_pragma buf in 
  GeneratedPragma

let parse_fixpoint_pragma buf pragma_str =
  let type_def = Parsers.Parser.read buf in
  let _ = Parsers.Parser.read buf in 
  let _ = Parsers.Parser.read buf in 
  let rule_body = Parsers.Parser.read buf in
  let pragma_end = Parsers.Parser.read buf in
  match type_def, rule_body, pragma_end with
  | Parsers.Entry.Decl (_,_,_,_,_), Parsers.Entry.Rules(_,_), Parsers.Entry.Pragma(_, _) ->
    let recno_opt = get_attr pragma_str recno_attr in
    (match recno_opt with
    | Some str -> 
        Some (FixpointPragma (type_def, rule_body, int_of_string str))
    | None -> missing_attr pragma_str recno_attr fixpoint_pragma
    )
  | _ ->  
    HLog.error ("Malformed fixpoint pragma: error in parsing content of pragma '" ^ pragma_str ^ "'"); 
    None

let parse_inductive_pragma _ _ = None (*TODO*)

let parse_pragma pragma_str buf = 
  match pragma_name pragma_str with
  | None -> None
  | Some name -> (
      if name = generated_pragma then
        Some (parse_generated_pragma buf)
      else if name = fixpoint_pragma then
        parse_fixpoint_pragma buf pragma_str
      else if name = inductive_pragma  then
        parse_inductive_pragma buf pragma_str 
      else ( 
        HLog.message("Found uknown pragma '" ^ pragma_str ^ "'");
        None
    )
  )

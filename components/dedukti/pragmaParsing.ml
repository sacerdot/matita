(*                     name     recno body-name*)
type fp_pragma_attrs = string * int * string

type export_pragma = 
  | GeneratedPragma
  (*                  type                   body                    attrs *)
  | FixpointPragma of (Parsers.Entry.entry * Parsers.Entry.entry * fp_pragma_attrs) list
  (*                  leftno *)
  | InductivePragma of int

let generated_pragma = "GENERATED"
let fixpoint_pragma = "FIXPOINT"
let fixpoint_body_pragma = "FIXPOINT_BODY"
let inductive_pragma = "INDUCTIVE"
let recno_attr = "RECNO"
let leftno_attr = "LEFTNO"
let body_attr = "BODY"
let name_regex = Str.regexp {|NAME=\([a-zA-Z0-9_]+\)|}
let ref_regex = Str.regexp {|REF=\([a-zA-Z0-9_]+\)|}
let recno_regex = Str.regexp (recno_attr ^ ":[a-z|A-Z|0-9]+=[a-z|A-Z|0-9]+")
let body_regex = Str.regexp (body_attr ^ ":[a-z|A-Z|0-9]+=[a-z|A-Z|0-9]+")

let failwith_log mex = 
  HLog.error mex;
  failwith mex

(* Given a string of type 'PRAGMA <BEGIN/GENERATED> <NAME> [ATTR=...]' returns the `NAME` part *)
let pragma_name pragma_str = 
  try 
    let splitted = String.split_on_char ' ' pragma_str in 
    Some (List.nth splitted 2)
  with _ -> None

let missing_attr pragma_str attr pragma_type =
  HLog.error ("Malformed " ^ pragma_type ^ " pragma: missing '" ^ attr ^ "' attribute in pragma '" ^ pragma_str ^ "' ");
  None

let filter_matching list regex = List.filter (fun s -> Str.string_match regex s 0) list
 
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

(** [bound_equal l1 l2 b] checks wheter the first [b] elements of [l1] are 
    equals to the first [b] elements of [l2] *)
let bound_equal l1 l2 b =
  let rec aux l1 l2 b =
   match l1,l2 with
   | _,_ when b=0 -> true
   | hd1::tl1,hd2::tl2 -> hd1=hd2 && aux tl1 tl2 (b-1)
   | _,_ -> false in
   aux l1 l2 b

(** [same_type p1 p2] check if the pragmas [p1] and [p2] are of the same type *)
let same_type pragma_1 pragma_2 =
  let p1 = String.split_on_char ' ' pragma_1 in
  let p2 = String.split_on_char ' ' pragma_2 in
  (* Just check the first three words: eg PRAGMA BEGIN NAME*)
  bound_equal p1 p2 3

let is_fixpoint_body_pragma pragma_str =
  let splitted = String.split_on_char ' ' pragma_str in
  (fixpoint_body_pragma = (List.nth splitted 1)) 

(** [read_until_pragma pragma buf] consumes [buf] until it finds an entry of 
    type 'Pragma' with string value equal to [pragma] and returns the entries *)
let rec read_until_pragma pragma buf = 
  let entry = Parsers.Parser.read buf in
  match entry with 
  | Parsers.Entry.Pragma(_, str) when str = pragma -> []
  | _ -> (entry :: read_until_pragma pragma buf)

let parse_generated_pragma buf = 
  let _ = read_until_pragma ("PRAGMA END " ^ generated_pragma) buf in 
  GeneratedPragma

(** If [str] is in the form "KEY:name=VALUE" [get_name_and_value_from_attr str] returns [(name, value)] *)
let get_name_and_value_from_attr str =
  let pattern = Str.regexp  {|\([A-Z]+:\)\([a-zA-Z0-9_]+\)=\([a-zA-Z0-9_]+\)|} in 
  if Str.string_match pattern str 0 then (
    let name = Str.matched_group 2 str in
    let value = Str.matched_group 3 str in
    (name, value) 
  ) else 
    failwith_log ("Cannot extract name and value from the string '" ^ str ^ "'")

let parse_name_only_attr str attr_regex=
  if Str.string_match attr_regex str 0 then 
    Some (Str.matched_group 1 str)
  else
    None

(** [find_attr_for_name name attr_list] find the attribute in [attr_list] which referes
    to [name]. An attriubte is seen like a pair name-value [string * string] *)
let rec find_attr_for_name name =
  function
  | [] -> None 
  | ((n, v) :: _) when n = name -> Some v  
  | (_ :: t) -> find_attr_for_name name t

(** [construct_fp_attr recnos bodies names] construct a [fp_pragma_attrs list] by 
    coupling togheter names and attributes *)
let rec construct_fp_attr recnos bodies =
  function
  | [] -> []
  | (name :: tail) -> 
    let recno_opt = find_attr_for_name name recnos in
    let body_opt = find_attr_for_name name bodies in
    (match recno_opt, body_opt with
    | Some(recno), Some(body) -> ((name, int_of_string(recno), body) :: (construct_fp_attr recnos bodies tail))
    | None, _ ->
        failwith_log "fixpoint pragma without recno attr"
    | _, None -> 
        failwith_log "fixpoint pragma without body attr"
    )

(** [parse_fp_attrs pragma_str] return a [fp_pragma_attrs] with the attributes
    found parsing [pragma_str] *)
let parse_fp_attrs pragma_str =
  let splitted = String.split_on_char ' ' pragma_str in 
  let names_opt = List.map (fun s -> parse_name_only_attr s name_regex) splitted in
  let names = List.map Option.get (List.filter Option.is_some names_opt) in
  let recnos = filter_matching splitted recno_regex in 
  let recnos'= List.map get_name_and_value_from_attr recnos in
  let bodies = filter_matching splitted body_regex in
  let bodies' = List.map get_name_and_value_from_attr bodies in
  construct_fp_attr recnos' bodies' names

let rec construct_fixpoint_pragma attributes entries =
  (* Find the entry of the list which holds the type of the fixpoint referenced by the name *)
  let rec find_type_entry name entries =
    match entries with
    | [] -> None
    | (Parsers.Entry.Decl(_, ident, _, _, _) as e :: _) when name = (Kernel.Basic.string_of_ident ident) ->
        Some e
    | (_::t) -> find_type_entry name t
  in
  (* Given a list of strings find the one matching REF attribute regex and return the value*)
  let rec find_ref_attr list = (
    match list with 
    | [] -> None
    | (h::t) ->
      let ref_val_opt = parse_name_only_attr h ref_regex in
      if Option.is_some ref_val_opt then 
        ref_val_opt
      else 
        find_ref_attr t
    ) in
  (* Find the entry of the list which holds the body of the fixpoint referenced by the name *)
  let rec find_body_entry body_name entries =
    match entries with 
      | [] -> None  
      | (Parsers.Entry.Pragma(_, str) :: e :: t) when is_fixpoint_body_pragma str ->
        let splitted = String.split_on_char ' ' str in
        let ref_opt = find_ref_attr splitted in 
        (match  ref_opt with
        | Some(ref_val) when ref_val = body_name -> Some e
        | _ -> find_body_entry body_name (e::t)
        )
      | (_ :: t) -> find_body_entry body_name t
  in
  match attributes with
  | []  -> []
  | ((name, _, body_name) as attr :: tail) -> 
    let typ = find_type_entry name entries in
    let body = find_body_entry body_name entries in
    (match typ, body with
    | Some t, Some b -> ((t, b, attr) :: construct_fixpoint_pragma tail entries)
    | None, _ -> failwith_log "Missing type while constructing fixpoint"
    | _ , None -> failwith_log "Missing body while constructing fixpoint"
    )

let parse_fixpoint_pragma buf pragma_str =
  let attributes = parse_fp_attrs pragma_str in
  let entries = read_until_pragma ("PRAGMA END " ^ fixpoint_pragma) buf in
  FixpointPragma(construct_fixpoint_pragma attributes entries)

let parse_inductive_pragma _ _ = None (*TODO*)

let parse_block pragma_str buf = 
  match pragma_name pragma_str with
  | None -> None
  | Some name -> (
      if name = generated_pragma then
        Some (parse_generated_pragma buf)
      else if name = fixpoint_pragma then
        Some (parse_fixpoint_pragma buf pragma_str)
      else if name = inductive_pragma  then
        parse_inductive_pragma buf pragma_str 
      else if name = fixpoint_body_pragma then (
        HLog.warn("Found fixpoint body pragma outside of a fixpoint");
        None
      ) else ( 
        HLog.message("Found uknown pragma '" ^ pragma_str ^ "'");
        None
      )
  )

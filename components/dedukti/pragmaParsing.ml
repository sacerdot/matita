(*                     name     recno *)
type fp_pragma_attrs = string * int

(*                      name     cons name list *)
type ind_pragma_attrs = string * string list

type export_pragma =
  | GeneratedPragma
  (*                  type                   body                  attrs *)
  | FixpointPragma of
      (Parsers.Entry.entry * Parsers.Entry.entry * fp_pragma_attrs) list
  (*                   leftno  type                  constructors               attrs                   match const entry *)
  | InductivePragma of
      int
      * (Parsers.Entry.entry * Parsers.Entry.entry list * ind_pragma_attrs) list
      * Parsers.Entry.entry list

let generated_pragma = "GENERATED"
let fixpoint_pragma = "FIXPOINT"
let fixpoint_body_pragma = "FIXPOINT_BODY"
let inductive_pragma = "INDUCTIVE"
let match_pragma = "MATCH"
let name_attr = "NAME"
let ref_attr = "REF"
let leftno_attr = "LEFTNO"
let recno_regex = Str.regexp {|.*RECNO:[a-zA-Z0-9_]+=[0-9]+|}
let body_regex = Str.regexp {|.*BODY:[a-zA-Z0-9_]+=[a-zA-Z0-9_]+|}
let cons_regex = Str.regexp {|.*CONS:[a-zA-Z0-9_]+=[a-zA-Z0-9_]+|}

let pragma_name_regex =
  Str.regexp
    {|PRAGMA\( BEGIN\| END\)? \([A-Za-z_]+\)\(( \|[A-Z])+(:[A-Za-z0-9]+)*=([a-zA-Z0-9_]+)( )*\)*|}

let failwith_log mex =
  HLog.error mex;
  failwith mex

(** Given a string of type 'PRAGMA <BEGIN/END> <NAME> [ATTR=...]' returns the `NAME` part *)
let pragma_name pragma_str =
  if Str.string_match pragma_name_regex pragma_str 0 then
    Str.matched_group 2 pragma_str
  else failwith "Unable to get name of pragma '" ^ pragma_str ^ "'"

let is_valid_export_pragma pragma_str =
  Str.string_match pragma_name_regex pragma_str 0

let filter_matching list regex =
  List.filter (fun s -> Str.string_match regex s 0) list

(** [parse_attr_named str] when s is in the form `<KEY>:<NAME>=<VALUE>` returns 
    [(KEY, NAME, VALUE)]
    *)
let parse_attr_named str =
  let pattern =
    Str.regexp {|\([A-Z_]+\):\([a-zA-Z0-9_]+\)=\([a-zA-Z0-9_]+\)|}
  in
  if Str.string_match pattern str 0 then
    let key = Str.matched_group 1 str in
    let name = Str.matched_group 2 str in
    let value = Str.matched_group 3 str in
    (key, name, value)
  else failwith_log ("Cannot extract attributes from " ^ str)

(** [parse_attr str] when s is in the form `<KEY>=<VALUE>` returns [(KEY, VALUE)] *)
let parse_attr str =
  let pattern = Str.regexp {|\([A-Z_]+\)=\([a-zA-Z0-9_]+\)|} in
  if Str.string_match pattern str 0 then
    let key = Str.matched_group 1 str in
    let value = Str.matched_group 2 str in
    (key, value)
  else failwith_log ("Cannot extract attributes from " ^ str)

let parse_attr_by_key key str =
  let pattern = Str.regexp ({|.*|} ^ key ^ {|=\([a-zA-Z0-9_]+\)|}) in
  if Str.string_match pattern str 0 then Some (Str.matched_group 1 str)
  else None

(** [find_snd_by_fst fst list] find all seconds members of a list of paris which have
    the first member equal to [fst]*)
let rec find_snd_by_fst fst = function
  | [] -> []
  | (k, v) :: t when k = fst -> v :: find_snd_by_fst fst t
  | _ :: t -> find_snd_by_fst fst t

(* [find_decl_with_name name entries] finds the [Decl] entry inside the [entries] list which has
   an ident that matches with [name]. *)
let rec find_decl_with_name name entries =
  match entries with
  | [] -> None
  | (Parsers.Entry.Decl (_, ident, _, _, _) as e) :: _
    when name = Kernel.Basic.string_of_ident ident ->
      Some e
  | _ :: t -> find_decl_with_name name t

(** [construct_fp_attr recnos names] construct a [fp_pragma_attrs list] by 
    coupling togheter names and attributes *)
let rec construct_fp_attr recnos = function
  | [] -> []
  | name :: tail -> (
      let recno_list = find_snd_by_fst name recnos in
      match recno_list with
      | [ recno ] ->
          (name, int_of_string recno) :: construct_fp_attr recnos tail
      | [] ->
          failwith_log
            ("fixpoint pragma without RECNO attr for name '" ^ name ^ "'")
      | _ ->
          failwith_log
            ("fixpoint pragma with too many RECNO attributes for name '" ^ name
           ^ "'"))

(** [parse_fp_attrs pragma_str] return a [fp_pragma_attrs] with the attributes
    found parsing [pragma_str] *)
let parse_fp_attrs pragma_str =
  let splitted = String.split_on_char ' ' pragma_str in
  let names_opt = List.map (parse_attr_by_key name_attr) splitted in
  let names = List.map Option.get (List.filter Option.is_some names_opt) in
  let recnos = filter_matching splitted recno_regex in
  let recnos' =
    List.map
      (fun r ->
        let _, n, v = parse_attr_named r in
        (n, v))
      recnos
  in
  construct_fp_attr recnos' names

let rec construct_fixpoint_pragma attributes entries =
  (* Given a list of strings find the one matching REF attribute regex and return the value*)
  let rec find_ref_attr list =
    match list with
    | [] -> None
    | h :: t ->
        let ref_val_opt = parse_attr_by_key ref_attr h in
        if Option.is_some ref_val_opt then ref_val_opt else find_ref_attr t
  in
  (* Find the entry of the list which holds the body of the fixpoint referenced by the name *)
  let rec find_body_entry name entries =
    match entries with
    | [] -> None
    | Parsers.Entry.Pragma (_, str) :: e :: t
      when pragma_name str = fixpoint_body_pragma -> (
        let splitted = String.split_on_char ' ' str in
        let ref_opt = find_ref_attr splitted in
        match ref_opt with
        | Some ref_val when ref_val = name -> Some e
        | _ -> find_body_entry name (e :: t))
    | _ :: t -> find_body_entry name t
  in
  match attributes with
  | [] -> []
  | ((name, _) as attr) :: tail -> (
      let typ = find_decl_with_name name entries in
      let body = find_body_entry name entries in
      match (typ, body) with
      | Some t, Some b -> (t, b, attr) :: construct_fixpoint_pragma tail entries
      | None, _ -> failwith_log "Missing type while constructing fixpoint"
      | _, None -> failwith_log "Missing body while constructing fixpoint")

let parse_fixpoint_pragma pragma_str entries =
  let attributes = parse_fp_attrs pragma_str in
  FixpointPragma (construct_fixpoint_pragma attributes entries)

let rec construct_ind_attr cons = function
  | [] -> []
  | name :: tail ->
      let cons_values = find_snd_by_fst name cons in
      (name, cons_values) :: construct_ind_attr cons tail

let parse_ind_attrs pragma_str =
  let splitted = String.split_on_char ' ' pragma_str in
  let names_opt = List.map (parse_attr_by_key name_attr) splitted in
  let names = List.map Option.get (List.filter Option.is_some names_opt) in
  let cons = filter_matching splitted cons_regex in
  let cons =
    List.map
      (fun c ->
        let _, n, v = parse_attr_named c in
        (n, v))
      cons
  in
  construct_ind_attr cons names

let construct_ind_pragma leftno attributes entries =
  let find_type_entry name entries =
    match find_decl_with_name name entries with
    | Some typ -> typ
    | None ->
        failwith_log
          ("Unable to find type entry for inductive with name '" ^ name ^ "'")
  in
  let find_cons_entry entries cons =
    match find_decl_with_name cons entries with
    | Some e -> e
    | None ->
        failwith_log
          ("Unable to find constructor entry for constructor '" ^ cons ^ "'")
  in
  let rec construct_ind_types attributes entries =
    match attributes with
    | [] -> []
    | ((name, conss) as att) :: t ->
        let type_entry = find_type_entry name entries in
        let cons_entries = List.map (find_cons_entry entries) conss in
        (type_entry, cons_entries, att) :: construct_ind_types t entries
  in
  let types = construct_ind_types attributes entries in
  (leftno, types)

let rec construct_match_pragma entries =
  match entries with
  | Parsers.Entry.Pragma (_, str)
    :: (Parsers.Entry.Decl (_, _, _, _, _) as match_const)
    :: t
    when pragma_name str = match_pragma ->
      match_const :: construct_match_pragma t
  | _ :: t -> construct_match_pragma t
  | [] -> []

let parse_inductive_pragma pragma_str entries =
  match parse_attr_by_key leftno_attr pragma_str with
  | None ->
      failwith_log
        ("Unable to find 'LEFTNO' attribute in inductive pragma with value: '"
       ^ pragma_str ^ "'")
  | Some value ->
      let leftno = int_of_string value in
      let attrs = parse_ind_attrs pragma_str in
      construct_ind_pragma leftno attrs entries

let parse_block name pragma_str entries =
  if name = generated_pragma then Some GeneratedPragma
  else if name = fixpoint_pragma then
    Some (parse_fixpoint_pragma pragma_str entries)
  else if name = inductive_pragma then
    let match_const = construct_match_pragma entries in
    let leftno, types = parse_inductive_pragma pragma_str entries in
    Some (InductivePragma (leftno, types, match_const))
  else (
    HLog.message
      ("Found uknown pragma block beginning with '" ^ pragma_str ^ "'");
    None)

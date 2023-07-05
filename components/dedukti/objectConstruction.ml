let const_tbl = Hashtbl.create 0

let failwith_log mex =
  HLog.error mex;
  failwith mex

let mkuri ~baseuri name ext = 
  NUri.uri_of_string (baseuri ^ "/" ^ name ^ "." ^ ext)

let first (a,_,_) = a

let cic_cic = Kernel.Basic.mk_mident "cic"
let cic_Term = Kernel.Basic.mk_name (Kernel.Basic.mk_mident "cic") (Kernel.Basic.mk_ident "Term")
let cic_lift = Kernel.Basic.mk_name (Kernel.Basic.mk_mident "cic") (Kernel.Basic.mk_ident "lift")
let cic_prod = Kernel.Basic.mk_name (Kernel.Basic.mk_mident "cic") (Kernel.Basic.mk_ident "prod")
let cic_Univ = Kernel.Basic.mk_name (Kernel.Basic.mk_mident "cic") (Kernel.Basic.mk_ident "Univ")
let cic_univ = Kernel.Basic.mk_name (Kernel.Basic.mk_mident "cic") (Kernel.Basic.mk_ident "univ")
let cic_type = Kernel.Basic.mk_name (Kernel.Basic.mk_mident "cic") (Kernel.Basic.mk_ident "type")
let cic_prop = Kernel.Basic.mk_name (Kernel.Basic.mk_mident "cic") (Kernel.Basic.mk_ident "prop")
let cic_z = Kernel.Basic.mk_name (Kernel.Basic.mk_mident "cic") (Kernel.Basic.mk_ident "z")
let cic_succ = Kernel.Basic.mk_name (Kernel.Basic.mk_mident "cic") (Kernel.Basic.mk_ident "s")

let rec calc_univ_dept  = function
  | Kernel.Term.Const(_, name) when Kernel.Basic.name_eq name cic_z -> 0
  | Kernel.Term.App(Kernel.Term.Const(_, f_name), a, []) when Kernel.Basic.name_eq f_name cic_succ -> 1 + (calc_univ_dept a)
  | _ -> failwith_log "Error loading universe dept"

let make_type_n_uri term =
  let univ_dept = calc_univ_dept term in
  if univ_dept >= 0 && univ_dept <= 4 then
    NUri.uri_of_string(Printf.sprintf "cic:/matita/pts/Type%d.univ" univ_dept) 
  else
    failwith_log (Format.sprintf "Univers number must be between 0 and 4. Got %d" univ_dept)

let rec construct_debrujin index = NCic.Rel(index + 1)

and construct_type term = NCic.Sort(NCic.Type [`Type,make_type_n_uri(term)])

and construct_prop = NCic.Sort(NCic.Prop)

and construct_const ~baseuri:_ name =  
  let ident = Kernel.Basic.id name in
  let str_ident = Kernel.Basic.string_of_ident ident in 
  match Hashtbl.find_opt const_tbl name with
  | Some reference -> NCic.Const reference
  (* It should not happen; the reference is bogus *)
  | None -> NCic.Const (NReference.reference_of_string ("cic:/" ^ str_ident  ^ "#dec"))

and construct_sort = function
  | Kernel.Term.App(Kernel.Term.Const(_, name), a1, []) when Kernel.Basic.name_eq name cic_type -> 
    construct_type a1
  | Kernel.Term.Const(_, name) when Kernel.Basic.name_eq name cic_prop -> 
    construct_prop
  | _ -> assert false

and construct_appl ~baseuri f a1 args =
  match f, args with 
  | Kernel.Term.Const(_, name), [t] when Kernel.Basic.name_eq name cic_Term -> 
    construct_term ~baseuri t
  | Kernel.Term.Const(_, name), [_; _;Kernel.Term.Lam(_, ident, Some typ, body)] 
    when Kernel.Basic.name_eq name cic_prod -> 
    construct_prod ~baseuri (Kernel.Basic.string_of_ident ident) typ body
  | Kernel.Term.Const(_, name), [_; a] 
    when Kernel.Basic.name_eq name cic_lift -> 
    construct_term ~baseuri a
  | Kernel.Term.Const(_, name), [_; _; Kernel.Term.Lam(_, _, None, _) ] 
    when Kernel.Basic.name_eq name cic_prod -> 
    assert false
  | Kernel.Term.Const(_, name), []
    when Kernel.Basic.name_eq name cic_univ || Kernel.Basic.name_eq name cic_Univ -> 
    construct_sort a1
  | Kernel.Term.Const(_, name), _ when Kernel.Basic.mident_eq (Kernel.Basic.md name) cic_cic ->
    assert false
  | _ -> 
    let translator = construct_term ~baseuri in
    let t = List.map translator (f :: a1 :: args) in
    NCic.Appl t 

and construct_lambda ~baseuri binder typ body = 
  let translator = construct_term ~baseuri in
  let typ' = translator typ in
  let body' = translator body in
  NCic.Lambda(binder, typ', body')

and construct_prod ~baseuri binder typ body = 
  let translator = construct_term ~baseuri in
  let typ' = translator typ in
  let body'= translator body in
  NCic.Prod(binder, typ', body')

and construct_term ~baseuri = function
  | Kernel.Term.DB(_, _, i) -> construct_debrujin i
  | Kernel.Term.Const(_,name) -> construct_const ~baseuri name
  | Kernel.Term.App(f, a, args) -> construct_appl ~baseuri f a args
  | Kernel.Term.Lam(_, ident, Some typ, body) -> construct_lambda ~baseuri (Kernel.Basic.string_of_ident ident) typ body
  | Kernel.Term.Lam(_, _, None, _) -> assert false
  | Kernel.Term.Pi(_, ident, typ , body) -> construct_prod ~baseuri (Kernel.Basic.string_of_ident ident) typ body
  | Kernel.Term.Kind -> assert false
  | Kernel.Term.Type(_) -> assert false

let construct_obj_kind ~baseuri typ body ident = 
  let typ = construct_term ~baseuri typ in
  let body = Option.map (construct_term ~baseuri) body in 
  let attrs = (`Implied, `Axiom, `Regular) in
  NCic.Constant([], ident, body, typ, attrs)

let constuct_obj status ~baseuri ident typ body =
  let str_ident = Kernel.Basic.string_of_ident ident in 
  let name = Kernel.Basic.mk_name (Kernel.Basic.mk_mident (Filename.basename baseuri)) ident in
  let uri = mkuri ~baseuri str_ident "con" in
  let obj_kind = construct_obj_kind ~baseuri typ body str_ident in
  let height = NCicTypeChecker.height_of_obj_kind status uri ~subst:[] obj_kind in 
  let reference = NReference.reference_of_spec uri (if body <> None then NReference.Def(height) else NReference.Decl) in
  assert (not (Hashtbl.mem const_tbl name));
  Hashtbl.add const_tbl name reference;
  (uri, height, [], [], obj_kind)

let rec extract_idents_from_pattern =
  function
    | Kernel.Rule.Var(_, ident, _,  []) ->
      [Kernel.Basic.string_of_ident ident]
    | Kernel.Rule.Var(_, ident, _, pat_list) ->
      let str_ident = Kernel.Basic.string_of_ident ident in 
      let others = List.flatten (List.map (fun pat -> extract_idents_from_pattern pat) pat_list) in
      (str_ident :: others)
    | Kernel.Rule.Pattern(_, _, []) -> []
    | Kernel.Rule.Pattern(_, _, pat_list) ->
      List.flatten (List.map (fun pat -> extract_idents_from_pattern pat) pat_list)
    | Kernel.Rule.Lambda(_, ident, pattern) -> 
      let str_ident = Kernel.Basic.string_of_ident ident in 
      (str_ident :: extract_idents_from_pattern pattern) 
    | Kernel.Rule.Brackets(_) -> []

let construct_fixpoint_body ~baseuri (rule: 'a Kernel.Rule.rule) typ recno = 
  let rec aux ~baseuri (rule: 'a Kernel.Rule.rule) idents typ recno recindex =
    match typ, idents with
    | NCic.Prod(_, source, target), (h::t) when recindex < recno -> 
      NCic.Lambda(h, source, (aux ~baseuri rule t target recno (recindex + 1)))
    | NCic.Prod(_, source, _), [h] when recindex >= recno ->
      let body = construct_term ~baseuri rule.Kernel.Rule.rhs in 
      NCic.Lambda(h, source, body)
    | _, []-> failwith_log "Not enough names when parsing fixpoint"
    | _ -> assert false
  in 
  let idents = extract_idents_from_pattern rule.Kernel.Rule.pat in
  aux ~baseuri rule idents typ recno 0

let construct_fixpoint_function ~baseuri (typ_entry, body_entry, attrs) = 
  let name, recno, _ = attrs in
  match typ_entry, body_entry with
  | Parsers.Entry.Decl(_, _, _, _, typ), Parsers.Entry.Rules(_, rule_list) ->
    let typ' = construct_term ~baseuri typ in
    let body' = construct_fixpoint_body ~baseuri (List.hd rule_list) typ' recno in
    ([], name, recno, typ', body')
  | _ -> failwith_log "Malformed error reconstructing fixpoint "

let name_of_decl ~baseuri decl =
  match decl with
  | Parsers.Entry.Decl(_, ident, _, _, _) -> 
     Kernel.Basic.mk_name (Kernel.Basic.mk_mident (Filename.basename baseuri)) ident
  | _ -> failwith_log "Cant generate a name from this type of entry"

let mkuri_from_decl ~baseuri decl ext =
  match decl with
  | Parsers.Entry.Decl(_, ident, _, _, _) -> 
    let str_ident = Kernel.Basic.string_of_ident ident in
    let name = Kernel.Basic.mk_name (Kernel.Basic.mk_mident (Filename.basename baseuri)) ident in
    name, mkuri ~baseuri str_ident ext
  | _ -> failwith_log "Cant generate an uri from this type of entry"

let construct_fixpoint status ~baseuri fixpoint_list =
  let _name,uri = mkuri_from_decl ~baseuri (first (List.nth fixpoint_list 0)) "FIXME" in
  let functions = List.map (fun fp -> construct_fixpoint_function ~baseuri fp) fixpoint_list in
  let f_attr = (`Implied, `Axiom, `Regular) in 
  let obj_kind = NCic.Fixpoint(true, functions, f_attr) in 
  let height = NCicTypeChecker.height_of_obj_kind status uri ~subst:[] obj_kind in 
  Some [(uri, height, [], [], obj_kind)]

let construct_inductive_constructor ~baseuri = function
    | Parsers.Entry.Decl(_,ident,_,_,term) -> 
      let t = construct_term ~baseuri term in 
      let name = Kernel.Basic.string_of_ident ident in 
      ([], name, t)
    | _ -> failwith_log "Malformed inductive type constructor"

let construct_inductive_type ~baseuri (typ, conss, attrs) =
  match typ with
  | Parsers.Entry.Decl(_,_,_,_,typ_term) ->
    let name, _ = attrs in
    let typ' = construct_term ~baseuri typ_term in
    let conss' = List.map (construct_inductive_constructor ~baseuri) conss in
    ([], name, typ', conss')
  | _ -> assert false
  
let construct_inductive status ~baseuri leftno types =
  let names = List.map (fun (typ,_,_) -> name_of_decl ~baseuri typ) types in 
  let _name,uri = mkuri_from_decl ~baseuri (first(List.nth types 0)) "ind" in

  List.iteri (fun i name -> 
    let reference = NReference.reference_of_spec uri (NReference.Ind(true,i,leftno)) in
    assert (not (Hashtbl.mem const_tbl name));
    Hashtbl.add const_tbl name reference;
  ) names;

  let i_attr = (`Implied, `Regular) in
  let types' = List.map (construct_inductive_type ~baseuri) types in
  let obj_kind = NCic.Inductive(true, leftno, types', i_attr) in 
  let height = NCicTypeChecker.height_of_obj_kind status uri ~subst:[] obj_kind in 
  (uri, height, [], [], obj_kind)

let split_match_const match_const = 
  let rec extract_cases entry leftno = (
    match entry with
    | NCic.Prod(_, typ, oth) when leftno > 0 -> 
      let cases, ind = extract_cases oth (leftno - 1) in
      (typ :: cases, ind)
    | NCic.Prod(_, typ, _)  -> [], typ
    | _ -> assert false
  ) in
  match match_const with
  | NCic.Prod(_, rt, cases) -> 
    let return_type = rt in
    let leftno= 2 in (* TODO *)
    let cases, ind = extract_cases cases leftno in
    (return_type, cases, ind)
  |  _ -> assert false

let construct_match status ~baseuri = function
  | Parsers.Entry.Decl (_,ident,_,_,typ) -> 
    let ident' = Kernel.Basic.string_of_ident ident in
    let uri = mkuri ~baseuri ident' "FIXMEMORE" in
    let typ' = construct_term ~baseuri typ in
    let ret_typ, cases, ind = split_match_const typ' in
    let reference = NReference.reference_of_string ("cic:/" ^ ident' ^ "#dec") in
    let match_term = NCic.Match(reference, ret_typ, ind, cases) in
    let attrs = (`Implied, `Axiom, `Regular) in
    let obj_kind = NCic.Constant([], ident', Some match_term, ret_typ, attrs) in
    let height = NCicTypeChecker.height_of_obj_kind status uri ~subst:[] obj_kind in 
    (uri, height, [], [], obj_kind)
  | _ -> failwith_log "match const must be a declaration"

let rec read_until_end_pragma pragma_name buf =
  try
    match Parsers.Parser.read buf with
    | Parsers.Entry.Pragma(_, str) when (PragmaParsing.pragma_name str) = pragma_name -> []
    | _ as entry -> entry :: (read_until_end_pragma pragma_name buf)
  with End_of_file -> failwith_log ("PRAGMA '" ^ pragma_name ^"'not closed")

let handle_pragma_block status ~baseuri buf pragma_string = 
  let pragma_name = PragmaParsing.pragma_name pragma_string in
  let entries = read_until_end_pragma pragma_name buf in
  match PragmaParsing.parse_block pragma_name pragma_string entries with
  | Some export_pragma -> (
      match export_pragma with
    | PragmaParsing.GeneratedPragma -> None
    | PragmaParsing.FixpointPragma(fixpoint_list) -> construct_fixpoint status ~baseuri fixpoint_list
    | PragmaParsing.InductivePragma(leftno, types, Some (_)) -> Some [
      (* construct_match status ~baseuri match_const; *)
      construct_inductive status ~baseuri leftno types
    ]
    | PragmaParsing.InductivePragma(leftno, types, None) -> Some [
      construct_inductive status ~baseuri leftno types]
    )
  | _ -> failwith "Unable to parse pragma block" 

let obj_of_entry status ~baseuri buf = function
   Parsers.Entry.Def (_,ident,_,_,Some typ,body) -> 
    Some[(constuct_obj status ~baseuri ident typ (Some body)) ]
  | Parsers.Entry.Def (_,_,_,_,None, _) ->
    assert false
  | Parsers.Entry.Decl (_,ident,_,_,typ) -> 
    Some[(constuct_obj status ~baseuri ident typ None) ]
  | Parsers.Entry.Pragma(_, str) -> 
    if PragmaParsing.is_valid_export_pragma str then
      handle_pragma_block status ~baseuri buf str
    else (
      HLog.warn("Found unknow pragma " ^ str);
      None
    )
  | Parsers.Entry.Rules(_, _) ->
    HLog.warn("Ignoring found rewriting rule");
    None
  | _ ->
    HLog.message("NOT IMPLEMENTED (other)");
    None (*TODO*)

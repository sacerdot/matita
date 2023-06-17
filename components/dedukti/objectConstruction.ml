let const_tbl = Hashtbl.create 0

let mkuri ~baseuri name = 
  NUri.uri_of_string (baseuri ^ "/" ^ name ^ ".con")

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
  | _ -> HLog.message("Error loading universe dept");
    assert false

    (* TODO check 0 4*)
let make_type_n_uri term = NUri.uri_of_string(Printf.sprintf "cic:/matita/pts/Type%d.univ" (calc_univ_dept term)) 
let rec construct_debrujin index = NCic.Rel(index + 1) (* TODO check if it is really 0based*)

and construct_type term = NCic.Sort(NCic.Type [`Type,make_type_n_uri(term)])

and construct_prop = NCic.Sort(NCic.Prop)

and construct_const ~baseuri name =  
  let ident = Kernel.Basic.id name in
  let str_ident = Kernel.Basic.string_of_ident ident in 
  let uri = mkuri ~baseuri str_ident in
  match Hashtbl.find_opt const_tbl uri with
  | Some reference -> NCic.Const reference
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
  let uri = mkuri ~baseuri str_ident in
  let obj_kind = construct_obj_kind ~baseuri typ body str_ident in
  let height = NCicTypeChecker.height_of_obj_kind status uri ~subst:[] obj_kind in 
  let reference = NReference.reference_of_spec uri (if body <> None then NReference.Def(height) else NReference.Decl) in
  assert (not (Hashtbl.mem const_tbl uri));
  Hashtbl.add const_tbl uri reference;
  (uri, 0, [], [], obj_kind)

let construct_fixpoint status ~baseuri typ_entry body_entry = 
  match typ_entry, body_entry with
  | Parsers.Entry.Decl(_, t_ident, _, _, typ), Parsers.Entry.Rules(_, _) ->
    let str_ident = Kernel.Basic.string_of_ident t_ident in 
    let uri = mkuri ~baseuri str_ident in
    let typ' = constuct_obj status ~baseuri t_ident typ None  in
    let body' = typ' in (*TODO translate body*)
    let ind_fun = ([], str_ident, 0, typ', body') in (* TODO recno *)
    let f_attr = (`Implied, `Axiom, `Regular) in 
    let obj_kind = (true, [ind_fun], f_attr) in 
    (uri, 0, [], [], obj_kind)
  | _ -> assert false (* TODO *)

let handle_pragma status ~baseuri = function
  | PragmaParsing.GeneratedPragma(_) -> None
  | PragmaParsing.FixpointPragma(_, type_entry, body_entry) ->
    Some (construct_fixpoint status ~baseuri type_entry body_entry)

(* TODO remove *)
let rec parse_rule = function
  [] -> HLog.message("-------") 
  | (h :: t) -> Kernel.Rule.pp_part_typed_rule Format.err_formatter h; parse_rule t

let obj_of_entry status ~baseuri buf = function
   Parsers.Entry.Def (_,ident,_,_,Some typ,body) -> 
    Some(constuct_obj status ~baseuri ident typ (Some body)) 
  | Parsers.Entry.Def (_,_,_,_,None, _) ->
    assert false
  | Parsers.Entry.Decl (_,ident,_,_,typ) -> 
    Some(constuct_obj status ~baseuri ident typ None) 
  | Parsers.Entry.Pragma(_, str) -> 
    let parsed_pragma = PragmaParsing.parse_pragma str buf in
    (match parsed_pragma with
    | Some pragma -> handle_pragma status ~baseuri pragma
    | None -> None(* TODO *))
  | Parsers.Entry.Rules(_, rules) ->
    Printf.printf "prinin rule";
    parse_rule rules;
    None
  | _ ->
    HLog.message("NOT IMPLEMENTED (other)");
    None (*TODO*)

let const_tbl = Hashtbl.create 0

let mkuri ~baseuri name = 
  NUri.uri_of_string (baseuri ^ "/" ^ name ^ ".con")

let cic_term = Kernel.Basic.mk_name (Kernel.Basic.mk_mident "cic") (Kernel.Basic.mk_ident "Term")
let cic_prod = Kernel.Basic.mk_name (Kernel.Basic.mk_mident "cic") (Kernel.Basic.mk_ident "prod")

let rec construct_debrujin index = NCic.Rel(index + 1) (* TODO check if it is really 0based*)

and construct_const ~baseuri name =  
  let ident = Kernel.Basic.id name in
  let str_ident = Kernel.Basic.string_of_ident ident in 
  let uri = mkuri ~baseuri str_ident in
  match Hashtbl.find_opt const_tbl uri with
  | Some reference -> NCic.Const reference
  | None -> NCic.Const (NReference.reference_of_string ("cic:/" ^ str_ident  ^ "#dec"))

and construct_appl ~baseuri f a1 args =
  match f, args with 
  | Kernel.Term.Const(_, name), [t] when Kernel.Basic.name_eq name cic_term -> 
    construct_term ~baseuri t
  | Kernel.Term.Const(_, name), [_; _;Kernel.Term.Lam(_, ident, Some typ, body)] 
    when Kernel.Basic.name_eq name cic_prod -> 
    construct_prod ~baseuri (Kernel.Basic.string_of_ident ident) typ body
  | Kernel.Term.Const(_, name), [_; _; Kernel.Term.Lam(_, _, None, _) ] 
    when Kernel.Basic.name_eq name cic_prod -> 
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

let obj_of_entry status ~baseuri = function
   Parsers.Entry.Def (_,ident,_,_,Some typ,body) -> 
    HLog.message("<>< Found def1");
    Some(constuct_obj status ~baseuri ident typ (Some body)) 
  | Parsers.Entry.Def (_,_,_,_,None, _) ->
    HLog.message("<>< Found def2");
    assert false
  | Parsers.Entry.Decl (_,ident,_,_,typ) -> 

    HLog.message("Found decl");
    Some(constuct_obj status ~baseuri ident typ None) 
  | _ -> HLog.message("NOT IMPLEMENTED ^_^\"");  None (*TODO*)

(* TODO: Forse baseuri e' gia' in status *)
let rec eval_from_dedukti_stream ~asserted ~baseuri status buf =
  try
   let entry = Parsers.Parser.read buf in
   Parsers.Entry.pp_entry Format.err_formatter entry ;
   let obj = obj_of_entry status ~baseuri entry in
   Option.iter (fun obj -> HLog.message("Tradotto!" ^ status#ppobj obj)) obj;
  (** let status = Option.fold ~none:status ~some:(NCicLibrary.add_obj status) obj in **)
   eval_from_dedukti_stream ~asserted ~baseuri status buf
  with
     End_of_file -> asserted, status


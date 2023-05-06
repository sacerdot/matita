let const_tbl = Hashtbl.create 0

let mkuri ~baseuri name = 
  NUri.uri_of_string (baseuri ^ "/" ^ name ^ ".con")

let rec construct_debrujin index = NCic.Rel(index + 1) (* TODO check if it is really 0based*)

and construct_const ~baseuri cname =  
  let reference = Hashtbl.find const_tbl cname in
  NCic.Const reference

and construct_appl ~baseuri f a1 args =
  let translator = construct_term_and_attrs ~baseuri:baseuri in
  let t = List.map translator (f :: a1 :: args) in
  NCic.Appl t 

and construct_lambda ~baseuri binder typ body = 
  let translator = construct_term_and_attrs ~baseuri:baseuri in
  let typ' = translator typ in
  let body' = translator body in
  NCic.Lambda(binder, typ', body')

and construct_prod ~baseuri binder typ body = 
  let translator = construct_term_and_attrs ~baseuri:baseuri in
  let typ' = translator typ in
  let body'= translator body in
  NCic.Prod(binder, typ', body')

and construct_term_and_attrs ~baseuri = function
  | Kernel.Term.DB(_, _, i) -> construct_debrujin i
  | Kernel.Term.Const(_,name) -> construct_const name
  | Kernel.Term.App(f, a, args) -> construct_appl ~baseuri:baseuri f a args
  | Kernel.Term.Lam(_, ident, typ, body) -> (match typ with
                                              | Some a -> construct_lambda ~baseuri:baseuri (Kernel.Basic.string_of_ident ident) a body
                                              | None -> assert false)
  | Kernel.Term.Pi(_, ident, typ , body) -> construct_prod ~baseuri:baseuri (Kernel.Basic.string_of_ident ident) typ body
  | Kernel.Term.Kind -> assert false
  | Kernel.Term.Type(_) -> assert false

let construct_obj_kind ~baseuri typ body ident = 
  let typ = construct_term_and_attrs ~baseuri typ in
  let body = Option.map (construct_term_and_attrs ~baseuri) body in 
  let attrs = (`Implied, `Axiom, `Regular) in
  NCic.Constant([], ident, body, typ, attrs)

let constuct_obj status ~baseuri ident typ body =
  let str_ident = Kernel.Base.string_of_ident ident in 
  let uri = mkuri ~baseuri str_ident in
  let obj_kind = construct_obj_kind ~baseuri:baseuri typ body str_ident in
  let height = NCicTypeChecker.height_of_obj_kind status uri ~subst:[] obj_kind in 
  let reference = NReference.Ref(uri, if body <> None then Def(height) else Decl) in 
  (* Register the new constant into the const table *)
  assert !(Hashtbl.mem const_tbl cname);
  Hashtbl.add const_tbl cname reference;
  (uri, 0, [], [], obj_kind)

let rec obj_of_entry status ~baseuri = function
   Parsers.Entry.Def (_,ident,_,_,Some typ,body) -> Some(constuct_obj status baseuri ident typ body) 
  | Parsers.Entry.Def (_,ident,_,_,None, _) -> assert false
  | Parsers.Entry.Decl (_,ident,_,_,_,typ) -> Some(constuct_obj status baseuri ident typ None) 
  | _ -> None (*TODO*)

(* TODO: Forse baseuri e' gia' in status *)
let rec eval_from_dedukti_stream ~asserted ~baseuri status buf =
  try
   let entry = Parsers.Parser.read buf in
   Parsers.Entry.pp_entry Format.err_formatter entry ;
   let obj = obj_of_entry status ~baseuri entry in
   let status = Option.fold ~none:status ~some:(NCicLibrary.add_obj status) obj in
   eval_from_dedukti_stream ~asserted ~baseuri status buf
  with
     End_of_file -> asserted, status


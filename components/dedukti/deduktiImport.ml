let const_tbl = Hashtbl.create 0

let name_and_uri_from_term ~baseuri = function
    Kernel.Term.Const(_, name) -> let str_ident = Kernel.Basic.string_of_ident (Kernel.Basic.id name) in
      let uri = NUri.uri_of_string (baseuri ^ "/" ^ str_ident ^ ".con") in
      (str_ident, uri)
    | Kernel.Term.App(_, _, _) -> assert false (*TODO what should we return if the term is an App?*)
    | _ -> assert false (* TODO *) 

let gen_const_name name = name (* TODO do something like "filename/constname" *)

let rec construct_debrujin index = NCic.Rel(index + 1) (* TODO check if it is really 0based*)

and construct_const name =  
  let cname = gen_const_name name in
  let reference = (cname, 0) in
  (* If not already present, register the new constant into the const table *)
  if !Hashtbl.mem const_tbl cname then
    Hashtbl.add const_tbl cname reference;
  NCic.Const reference (*TODO*)

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

let construct_obj_kind ~baseuri term ident = 
  let typ = construct_term_and_attrs ~baseuri:baseuri term in
  let attrs = (`Implied, `Axiom, `Regular) in
  NCic.Constant([], ident, None, typ, attrs)

let constuct_obj ~baseuri term =
  let (str_ident, uri) = name_and_uri_from_term ~baseuri:baseuri term in
  (uri, 0, [], [], construct_obj_kind ~baseuri:baseuri term str_ident)

let rec obj_of_entry ~baseuri = function
   Parsers.Entry.Def (_,_,_,_,_,term) -> Some(constuct_obj baseuri term) 
  | _ -> None (*TODO*)

(* TODO: Forse baseuri e' gia' in status *)
let rec eval_from_dedukti_stream ~asserted ~baseuri status buf =
  try
   let entry = Parsers.Parser.read buf in
   Parsers.Entry.pp_entry Format.err_formatter entry ;
   let obj = obj_of_entry ~baseuri entry in
   let status = Option.fold ~none:status ~some:(NCicLibrary.add_obj status) obj in
   eval_from_dedukti_stream ~asserted ~baseuri status buf
  with
     End_of_file -> asserted, status


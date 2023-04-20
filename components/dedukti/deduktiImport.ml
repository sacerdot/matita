(* 
TODO remove
let obj_of_entry ~baseuri =
 function
    Parsers.Entry.Decl (_,name,_,_,_)
  | Parsers.Entry.Def (_,name,_,_,_,_) ->
     prerr_endline "OK OK" ;
     let name = Kernel.Basic.string_of_ident name in
     let uri = NUri.uri_of_string (baseuri ^ "/" ^ name ^ ".con") in
     prerr_endline ("NAME =#" ^ name ^ "#") ;
     prerr_endline ("URI =" ^ NUri.string_of_uri uri) ;
     prerr_endline ("REF = " ^ NReference.string_of_reference ((NReference.reference_of_spec uri NReference.Decl))) ;
     let attrs = (`Implied, `Axiom, `Regular) in
     let typ = NCic.Sort NCic.Prop in
     Some name, Some (uri, 0, [], [], NCic.Constant ([], name, None, typ, attrs))
  | _ -> None, None (* TODO *)

  (* Forse baseuri e' gia' in status *)
let rec eval_from_dedukti_stream ~asserted ~baseuri status buf =
  try
   let entry = Parsers.Parser.read buf in
   Parsers.Entry.pp_entry Format.err_formatter entry ;
   let name,obj = obj_of_entry ~baseuri entry in
   let status = Option.fold ~none:status ~some:(NCicLibrary.add_obj status) obj in
   Option.iter (fun name -> prerr_endline ("TROVATO? " ^ string_of_int (List.length (NCicLibrary.resolve name)))) name;
   eval_from_dedukti_stream ~asserted ~baseuri status buf
  with
     End_of_file -> asserted, status

  *)


let name_and_uri_from_term ~baseuri = function
    Kernel.Term.Const(_, name) -> let str_ident = Kernel.Basic.string_of_ident (Kernel.Basic.id name) in
      let uri = NUri.uri_of_string (baseuri ^ "/" ^ str_ident ^ ".con") in
      (str_ident, uri)
    | Kernel.Term.App(_, _, _) -> assert false (*TODO*)
    | _ -> assert false (* TODO *) 

let rec construct_const =  
  let attrs = (`Implied, `Axiom, `Regular) in
  let typ = NCic.Sort NCic.Prop in
  (typ, attrs)

and construct_appl ~baseuri f a1 args =
  let translator = construct_term_and_attrs ~baseuri:baseuri in
  let (t_f, _) = translator f in
  let (t_a1, _) = translator a1 in
  (* Take only terms. Ignore attrs *)
  let t_args = List.map (fun x -> let (t, _) = translator x in t) args in
  let typ = NCic.Appl([t_f; t_a1] @ t_args) in
  let attrs = (`Implied, `Axiom, `Regular) in (* TODO check if attrs are good*)
  (typ, attrs)

and construct_lambda ~baseuri binder arg body = 
  let translator = construct_term_and_attrs ~baseuri:baseuri in
  let (arg', _) = translator arg in
  let (body', _) = translator body in
  let typ = NCic.Lambda(binder, arg', body') in
  let attrs = (`Implied, `Axiom, `Regular) in (* TODO check if attrs are good*)
  (typ, attrs)

and construct_prod ~baseuri binder arg body = 
  let translator = construct_term_and_attrs ~baseuri:baseuri in
  let (arg', _) = translator arg in
  let (body', _) = translator body in
  let typ = NCic.Prod(binder, arg', body') in
  let attrs = (`Implied, `Axiom, `Regular) in (* TODO check if attrs are good*)
  (typ, attrs)

and construct_term_and_attrs ~baseuri = function
  Kernel.Term.Const(_,_) -> construct_const
    | Kernel.Term.App(f, a, args) -> construct_appl ~baseuri:baseuri f a args
    | Kernel.Term.Lam(_, _, None, _) -> assert false (* TODO understand what to do with no args func *) 
    | Kernel.Term.Lam(_, ident, arg, body) -> construct_lambda ~baseuri:baseuri (Kernel.Basic.string_of_ident ident) (Option.get arg) body
    | Kernel.Term.Pi(_, ident, arg, body) -> construct_prod ~baseuri:baseuri (Kernel.Basic.string_of_ident ident) arg body
    |_ -> assert false (*TODO*)

let construct_obj_kind ~baseuri term ident = 
  let (typ, attrs) = construct_term_and_attrs ~baseuri:baseuri term in
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


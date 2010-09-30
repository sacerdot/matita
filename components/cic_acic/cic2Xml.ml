(* Copyright (C) 2000-2004, HELM Team.
 * 
 * This file is part of HELM, an Hypertextual, Electronic
 * Library of Mathematics, developed at the Computer Science
 * Department, University of Bologna, Italy.
 * 
 * HELM is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 * 
 * HELM is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with HELM; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston,
 * MA  02111-1307, USA.
 * 
 * For details, see the HELM World-Wide-Web page,
 * http://helm.cs.unibo.it/
 *)

(* $Id$ *)

(*CSC codice cut & paste da cicPp e xmlcommand *)

exception NotImplemented;;

let dtdname ~ask_dtd_to_the_getter dtd =
 if ask_dtd_to_the_getter then
  Helm_registry.get "getter.url" ^ "getdtd?uri=" ^ dtd
 else
  "http://mowgli.cs.unibo.it/dtd/" ^ dtd
;;

let param_attribute_of_params params =
 String.concat " " (List.map UriManager.string_of_uri params)
;;

(*CSC ottimizzazione: al posto di curi cdepth (vedi codice) *)
let print_term ?ids_to_inner_sorts =
 let find_sort name id =
  match ids_to_inner_sorts with
     None -> []
   | Some ids_to_inner_sorts ->
      [None,name,Cic2acic.string_of_sort (Hashtbl.find ids_to_inner_sorts id)]
 in
 let rec aux =
  let module C = Cic in
  let module X = Xml in
  let module U = UriManager in
    function
       C.ARel (id,idref,n,b) ->
        let sort = find_sort "sort" id in
         X.xml_empty "REL"
          (sort @
           [None,"value",(string_of_int n) ; None,"binder",b ; None,"id",id ;
           None,"idref",idref])
     | C.AVar (id,uri,exp_named_subst) ->
        let sort = find_sort "sort" id in
         aux_subst uri
          (X.xml_empty "VAR"
            (sort @ [None,"uri",U.string_of_uri uri;None,"id",id]))
          exp_named_subst
     | C.AMeta (id,n,l) ->
        let sort = find_sort "sort" id in
         X.xml_nempty "META"
          (sort @ [None,"no",(string_of_int n) ; None,"id",id])
          (List.fold_left
            (fun i t ->
              match t with
                 Some t' ->
                  [< i ; X.xml_nempty "substitution" [] (aux t') >]
               | None ->
                  [< i ; X.xml_empty "substitution" [] >]
            ) [< >] l)
     | C.ASort (id,s) ->
        let string_of_sort s =
          Cic2acic.string_of_sort (Cic2acic.sort_of_sort s)
        in
         X.xml_empty "SORT" [None,"value",(string_of_sort s) ; None,"id",id]
     | C.AImplicit _ -> raise NotImplemented
     | C.AProd (last_id,_,_,_) as prods ->
        let rec eat_prods =
         function
            C.AProd (id,n,s,t) ->
             let prods,t' = eat_prods t in
              (id,n,s)::prods,t'
          | t -> [],t
        in
         let prods,t = eat_prods prods in
          let sort = find_sort "type" last_id in
           X.xml_nempty "PROD" sort
            [< List.fold_left
                (fun i (id,binder,s) ->
                  let sort = find_sort "type" (Cic2acic.source_id_of_id id) in
                   let attrs =
                    sort @ ((None,"id",id)::
                     match binder with
                        C.Anonymous -> []
                      | C.Name b -> [None,"binder",b])
                   in
                    [< i ; X.xml_nempty "decl" attrs (aux s) >]
                ) [< >] prods ;
               X.xml_nempty "target" [] (aux t)
            >]
     | C.ACast (id,v,t) ->
        let sort = find_sort "sort" id in
         X.xml_nempty "CAST" (sort @ [None,"id",id])
          [< X.xml_nempty "term" [] (aux v) ;
             X.xml_nempty "type" [] (aux t)
          >]
     | C.ALambda (last_id,_,_,_) as lambdas ->
        let rec eat_lambdas =
         function
            C.ALambda (id,n,s,t) ->
             let lambdas,t' = eat_lambdas t in
              (id,n,s)::lambdas,t'
          | t -> [],t
        in
         let lambdas,t = eat_lambdas lambdas in
          let sort = find_sort "sort" last_id in
           X.xml_nempty "LAMBDA" sort
            [< List.fold_left
                (fun i (id,binder,s) ->
                  let sort = find_sort "type" (Cic2acic.source_id_of_id id) in
                   let attrs =
                    sort @ ((None,"id",id)::
                     match binder with
                        C.Anonymous -> []
                      | C.Name b -> [None,"binder",b])
                   in
                    [< i ; X.xml_nempty "decl" attrs (aux s) >]
                ) [< >] lambdas ;
               X.xml_nempty "target" [] (aux t)
            >]
     | C.ALetIn (xid,C.Anonymous,s,ty,t) ->
       assert false
     | C.ALetIn (last_id,C.Name _,_,_,_) as letins ->
        let rec eat_letins =
         function
            C.ALetIn (id,n,s,ty,t) ->
             let letins,t' = eat_letins t in
              (id,n,s,ty)::letins,t'
          | t -> [],t
        in
         let letins,t = eat_letins letins in
          let sort = find_sort "sort" last_id in
           X.xml_nempty "LETIN" sort
            [< List.fold_left
                (fun i (id,binder,s,ty) ->
                  let sort = find_sort "sort" id in
                   let attrs =
                    sort @ ((None,"id",id)::
                     match binder with
                        C.Anonymous -> []
                      | C.Name b -> [None,"binder",b])
                   in
                    [< i ; X.xml_nempty "def" attrs [< aux s ; aux ty >] >]
                ) [< >] letins ;
               X.xml_nempty "target" [] (aux t)
            >]
     | C.AAppl (id,li) ->
        let sort = find_sort "sort" id in
         X.xml_nempty "APPLY" (sort @ [None,"id",id])
          [< (List.fold_right (fun x i -> [< (aux x) ; i >]) li [<>])
          >]
     | C.AConst (id,uri,exp_named_subst) ->
        let sort = find_sort "sort" id in
         aux_subst uri
          (X.xml_empty "CONST"
            (sort @ [None,"uri",(U.string_of_uri uri) ; None,"id",id])
          ) exp_named_subst
     | C.AMutInd (id,uri,i,exp_named_subst) ->
        aux_subst uri
         (X.xml_empty "MUTIND"
           [None, "uri", (U.string_of_uri uri) ;
            None, "noType", (string_of_int i) ;
            None, "id", id]
         ) exp_named_subst
     | C.AMutConstruct (id,uri,i,j,exp_named_subst) ->
        let sort = find_sort "sort" id in
         aux_subst uri
          (X.xml_empty "MUTCONSTRUCT"
            (sort @
             [None,"uri", (U.string_of_uri uri) ;
              None,"noType",(string_of_int i) ;
              None,"noConstr",(string_of_int j) ;
              None,"id",id])
          ) exp_named_subst
     | C.AMutCase (id,uri,typeno,ty,te,patterns) ->
        let sort = find_sort "sort" id in
         X.xml_nempty "MUTCASE"
          (sort @
           [None,"uriType",(U.string_of_uri uri) ;
            None,"noType", (string_of_int typeno) ;
            None,"id", id])
          [< X.xml_nempty "patternsType" [] [< (aux ty) >] ;
             X.xml_nempty "inductiveTerm" [] [< (aux te) >] ;
             List.fold_right
              (fun x i -> [< X.xml_nempty "pattern" [] [< aux x >] ; i>])
              patterns [<>]
          >]
     | C.AFix (id, no, funs) ->
        let sort = find_sort "sort" id in
         X.xml_nempty "FIX"
          (sort @ [None,"noFun", (string_of_int no) ; None,"id",id])
          [< List.fold_right
              (fun (id,fi,ai,ti,bi) i ->
                [< X.xml_nempty "FixFunction"
                    [None,"id",id ; None,"name", fi ;
                     None,"recIndex", (string_of_int ai)]
                    [< X.xml_nempty "type" [] [< aux ti >] ;
                       X.xml_nempty "body" [] [< aux bi >]
                    >] ;
                   i
                >]
              ) funs [<>]
          >]
     | C.ACoFix (id,no,funs) ->
        let sort = find_sort "sort" id in
         X.xml_nempty "COFIX"
          (sort @ [None,"noFun", (string_of_int no) ; None,"id",id])
          [< List.fold_right
              (fun (id,fi,ti,bi) i ->
                [< X.xml_nempty "CofixFunction" [None,"id",id ; None,"name", fi]
                    [< X.xml_nempty "type" [] [< aux ti >] ;
                       X.xml_nempty "body" [] [< aux bi >]
                    >] ;
                   i
                >]
              ) funs [<>]
          >]
 and aux_subst buri target subst =
(*CSC: I have now no way to assign an ID to the explicit named substitution *)
  let id = None in
   if subst = [] then
    target
   else
    Xml.xml_nempty "instantiate"
     (match id with None -> [] | Some id -> [None,"id",id])
     [< target ;
        List.fold_left
         (fun i (uri,arg) ->
           let relUri =
            let buri_frags =
             Str.split (Str.regexp "/") (UriManager.string_of_uri buri) in
            let uri_frags = 
             Str.split (Str.regexp "/") (UriManager.string_of_uri uri)  in
             let rec find_relUri buri_frags uri_frags =
              match buri_frags,uri_frags with
                 [_], _ -> String.concat "/" uri_frags
               | he1::tl1, he2::tl2 ->
                  assert (he1 = he2) ;
                  find_relUri tl1 tl2
               | _,_ -> assert false (* uri is not relative to buri *)
             in
              find_relUri buri_frags uri_frags
           in
            [< i ; Xml.xml_nempty "arg" [None,"relUri", relUri] (aux arg) >]
         ) [<>] subst
     >]
  in
   aux
;;

let xml_of_attrs generate_attributes attributes =
  let class_of = function
    | `Coercion n -> 
        Xml.xml_empty "class" [None,"value","coercion";None,"arity",string_of_int n]
    | `Elim s ->
        Xml.xml_nempty "class" [None,"value","elim"]
         [< Xml.xml_empty
             "SORT" [None,"value",
                      (Cic2acic.string_of_sort (Cic2acic.sort_of_sort s)) ;
                     None,"id","elimination_sort"] >]
    | `Record field_names ->
        Xml.xml_nempty "class" [None,"value","record"]
         (List.fold_right
           (fun (name,coercion,arity) res ->
             [< Xml.xml_empty "field" 
                [None,"name",
                  if coercion then 
                    name ^ " coercion " ^ string_of_int arity 
                  else 
                    name]; 
              res >]
           ) field_names [<>])
    | `Projection -> Xml.xml_empty "class" [None,"value","projection"]
    | `InversionPrinciple -> Xml.xml_empty "class" [None,"value","inversion"]
  in
  let flavour_of = function
    | `Definition -> Xml.xml_empty "flavour" [None, "value", "definition"]
    | `MutualDefinition ->
        Xml.xml_empty "flavour" [None, "value", "mutual_definition"]
    | `Fact -> Xml.xml_empty "flavour" [None, "value", "fact"]
    | `Lemma -> Xml.xml_empty "flavour" [None, "value", "lemma"]
    | `Remark -> Xml.xml_empty "flavour" [None, "value", "remark"]
    | `Theorem -> Xml.xml_empty "flavour" [None, "value", "theorem"]
    | `Variant -> Xml.xml_empty "flavour" [None, "value", "variant"]
    | `Axiom -> Xml.xml_empty "flavour" [None, "value", "axiom"]
  in
  let xml_attr_of = function
    | `Generated -> Xml.xml_empty "generated" []
    | `Class c -> class_of c
    | `Flavour f -> flavour_of f
  in
  let xml_attrs =
   List.fold_right 
    (fun attr res -> [< xml_attr_of attr ; res >]) attributes [<>]
  in
   if generate_attributes then Xml.xml_nempty "attributes" [] xml_attrs else [<>]

let print_object uri 
  ?ids_to_inner_sorts ?(generate_attributes=true) ~ask_dtd_to_the_getter obj =
 let module C = Cic in
 let module X = Xml in
 let module U = UriManager in
  let dtdname = dtdname ~ask_dtd_to_the_getter "cic.dtd" in
   match obj with
       C.ACurrentProof (id,idbody,n,conjectures,bo,ty,params,obj_attrs) ->
        let params' = param_attribute_of_params params in
        let xml_attrs = xml_of_attrs generate_attributes obj_attrs in
        let xml_for_current_proof_body =
(*CSC: Should the CurrentProof also have the list of variables it depends on? *)
(*CSC: I think so. Not implemented yet.                                       *)
         X.xml_nempty "CurrentProof"
          [None,"of",UriManager.string_of_uri uri ; None,"id", id]
          [< xml_attrs;
            List.fold_left
              (fun i (cid,n,canonical_context,t) ->
                [< i ;
                   X.xml_nempty "Conjecture"
                    [None,"id",cid ; None,"no",(string_of_int n)]
                    [< List.fold_left
                        (fun i (hid,t) ->
                          [< (match t with
                                 Some (n,C.ADecl t) ->
                                  X.xml_nempty "Decl"
                                   (match n with
                                       C.Name n' ->
                                        [None,"id",hid;None,"name",n']
                                     | C.Anonymous -> [None,"id",hid])
                                   (print_term ?ids_to_inner_sorts t)
                               | Some (n,C.ADef (t,_)) ->
                                  X.xml_nempty "Def"
                                   (match n with
                                       C.Name n' ->
                                        [None,"id",hid;None,"name",n']
                                     | C.Anonymous -> [None,"id",hid])
                                   (print_term ?ids_to_inner_sorts t)
                              | None -> X.xml_empty "Hidden" [None,"id",hid]
                             ) ;
                             i
                          >]
                        ) [< >] canonical_context ;
                       X.xml_nempty "Goal" []
                        (print_term ?ids_to_inner_sorts t)
                    >]
                >])
              [< >] conjectures ;
             X.xml_nempty "body" [] (print_term ?ids_to_inner_sorts bo) >]
        in
        let xml_for_current_proof_type =
         X.xml_nempty "ConstantType"
          [None,"name",n ; None,"params",params' ; None,"id", id]
          (print_term ?ids_to_inner_sorts ty)
        in
        let xmlbo =
         [< X.xml_cdata "<?xml version=\"1.0\" encoding=\"ISO-8859-1\"?>\n" ;
            X.xml_cdata ("<!DOCTYPE CurrentProof SYSTEM \""^ dtdname ^ "\">\n");
            xml_for_current_proof_body
         >] in
        let xmlty =
         [< X.xml_cdata "<?xml version=\"1.0\" encoding=\"ISO-8859-1\"?>\n" ;
            X.xml_cdata ("<!DOCTYPE ConstantType SYSTEM \""^ dtdname ^ "\">\n");
            xml_for_current_proof_type
         >]
        in
         xmlty, Some xmlbo
     | C.AConstant (id,idbody,n,bo,ty,params,obj_attrs) ->
        let params' = param_attribute_of_params params in
        let xml_attrs = xml_of_attrs generate_attributes obj_attrs in
        let xmlbo =
         match bo with
            None -> None
          | Some bo ->
             Some
              [< X.xml_cdata
                  "<?xml version=\"1.0\" encoding=\"ISO-8859-1\"?>\n" ;
                 X.xml_cdata
                  ("<!DOCTYPE ConstantBody SYSTEM \"" ^ dtdname ^ "\">\n") ;
                 X.xml_nempty "ConstantBody"
                  [None,"for",UriManager.string_of_uri uri ;
                   None,"params",params' ; None,"id", id]
                  [< print_term ?ids_to_inner_sorts bo >]
              >]
        in
        let xmlty =
         [< X.xml_cdata "<?xml version=\"1.0\" encoding=\"ISO-8859-1\"?>\n" ;
            X.xml_cdata ("<!DOCTYPE ConstantType SYSTEM \""^ dtdname ^ "\">\n");
             X.xml_nempty "ConstantType"
              [None,"name",n ; None,"params",params' ; None,"id", id]
              [< xml_attrs; print_term ?ids_to_inner_sorts ty >]
         >]
        in
         xmlty, xmlbo
     | C.AVariable (id,n,bo,ty,params,obj_attrs) ->
        let params' = param_attribute_of_params params in
        let xml_attrs = xml_of_attrs generate_attributes obj_attrs in
        let xmlbo =
         match bo with
            None -> [< >]
          | Some bo ->
             X.xml_nempty "body" [] [< print_term ?ids_to_inner_sorts bo >]
        in
        let aobj =
         [< X.xml_cdata "<?xml version=\"1.0\" encoding=\"ISO-8859-1\"?>\n" ;
            X.xml_cdata ("<!DOCTYPE Variable SYSTEM \"" ^ dtdname ^ "\">\n");
             X.xml_nempty "Variable"
              [None,"name",n ; None,"params",params' ; None,"id", id]
              [< xml_attrs; xmlbo;
                 X.xml_nempty "type" [] (print_term ?ids_to_inner_sorts ty)
              >]
         >]
        in
         aobj, None
     | C.AInductiveDefinition (id,tys,params,nparams,obj_attrs) ->
        let params' = param_attribute_of_params params in
        let xml_attrs = xml_of_attrs generate_attributes obj_attrs in
         [< X.xml_cdata "<?xml version=\"1.0\" encoding=\"ISO-8859-1\"?>\n" ;
            X.xml_cdata
             ("<!DOCTYPE InductiveDefinition SYSTEM \"" ^ dtdname ^ "\">\n") ;
            X.xml_nempty "InductiveDefinition"
             [None,"noParams",string_of_int nparams ;
              None,"id",id ;
              None,"params",params']
             [< xml_attrs;
                (List.fold_left
                  (fun i (id,typename,finite,arity,cons) ->
                    [< i ;
                       X.xml_nempty "InductiveType"
                        [None,"id",id ; None,"name",typename ;
                         None,"inductive",(string_of_bool finite)
                        ]
                        [< X.xml_nempty "arity" []
                            (print_term ?ids_to_inner_sorts arity) ;
                           (List.fold_left
                            (fun i (name,lc) ->
                              [< i ;
                                 X.xml_nempty "Constructor"
                                  [None,"name",name]
                                  (print_term ?ids_to_inner_sorts lc)
                              >]) [<>] cons
                           )
                        >]
                    >]
                  ) [< >] tys
                )
             >]
         >], None
;;

let
 print_inner_types curi ~ids_to_inner_sorts ~ids_to_inner_types
  ~ask_dtd_to_the_getter
=
 let module C2A = Cic2acic in
 let module X = Xml in
  let dtdname = dtdname ~ask_dtd_to_the_getter "cictypes.dtd" in
   [< X.xml_cdata "<?xml version=\"1.0\" encoding=\"ISO-8859-1\"?>\n" ;
      X.xml_cdata
       ("<!DOCTYPE InnerTypes SYSTEM \"" ^ dtdname ^ "\">\n") ;
      X.xml_nempty "InnerTypes" [None,"of",UriManager.string_of_uri curi]
       (Hashtbl.fold
         (fun id {C2A.annsynthesized = synty ; C2A.annexpected = expty} x ->
           [< x ;
              X.xml_nempty "TYPE" [None,"of",id]
               [< X.xml_nempty "synthesized" []
	         [< print_term ~ids_to_inner_sorts synty >] ;
                 match expty with
                   None -> [<>]
                 | Some expty' -> X.xml_nempty "expected" []
                    [< print_term ~ids_to_inner_sorts expty' >]
               >]
           >]
         ) ids_to_inner_types [<>]
       )
   >]
;;

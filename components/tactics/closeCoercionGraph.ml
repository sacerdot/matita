(* Copyright (C) 2005, HELM Team.
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

(* $Id: cicCoercion.ml 7077 2006-12-05 15:44:54Z fguidi $ *)

let debug = false 
let debug_print s = if debug then prerr_endline (Lazy.force s) else ()

(* given the new coercion uri from src to tgt returns the list 
 * of new coercions to create. the list elements are
 * (source, list of coercions to follow, target)
 *)
let get_closure_coercions src tgt uri coercions =
  let enrich (uri,sat,_) tgt =
   let arity = match tgt with CoercDb.Fun n -> n | _ -> 0 in
    uri,sat,arity
  in
  let uri = enrich uri tgt in
  let eq_carr ?exact s t = 
    debug_print(lazy(CoercDb.string_of_carr s^" VS "^CoercDb.string_of_carr t));
    let rc = CoercDb.eq_carr ?exact s t in
    debug_print(lazy(string_of_bool rc));
    rc
  in
  match src,tgt with
  | CoercDb.Uri _, CoercDb.Uri _ ->
      debug_print (lazy ("Uri, Uri4"));
      let c_from_tgt = 
        List.filter 
          (fun (f,t,_) -> 
             debug_print (lazy ("Uri, Uri3"));
             eq_carr f tgt) 
          coercions 
      in
      let c_to_src = 
        List.filter 
          (fun (f,t,_) -> 
             debug_print (lazy ("Uri, Uri2"));
             eq_carr t src) 
          coercions 
      in
        (HExtlib.flatten_map 
          (fun (_,t,ul) -> 
             if eq_carr ~exact:true src t then [] else
             List.map (fun u -> src,[uri; enrich u t],t) ul) c_from_tgt) @
        (HExtlib.flatten_map 
          (fun (s,t,ul) -> 
             if eq_carr ~exact:true s tgt then [] else
             List.map (fun u -> s,[enrich u t; uri],tgt) ul) c_to_src) @
        (HExtlib.flatten_map 
          (fun (s,t1,u1l) ->
            HExtlib.flatten_map 
              (fun (_,t,u2l) ->
                HExtlib.flatten_map
                  (fun u1 ->
                  debug_print (lazy ("Uri, Uri1"));
                    if  eq_carr ~exact:true s t
                     || eq_carr ~exact:true s tgt
                     || eq_carr ~exact:true src t
                    then [] else
                    List.map 
                      (fun u2 -> (s,[enrich u1 t1;uri;enrich u2 t],t)) 
                      u2l)
                  u1l) 
              c_from_tgt) 
          c_to_src)
  | _ -> [] (* do not close in case source or target is not an indty ?? *)
;;

exception UnableToCompose

(* generate_composite (c2 (c1 s)) in the universe graph univ
   both living in the same context and metasenv

    c2 ?p2 (c1 ?p1 ?x ?s1) ?s2

    where:
     ?pn + 1 + ?sn = count_pi n - arity n
*)
let generate_composite' (c1,sat1,arity1) (c2,sat2,arity2) context metasenv univ=
  let original_metasenv = metasenv in 
  let c1_ty,univ = CicTypeChecker.type_of_aux' metasenv context c1 univ in
  let c2_ty,univ = CicTypeChecker.type_of_aux' metasenv context c2 univ in
  let rec mk_implicits = function
    | 0 -> [] | n -> (Cic.Implicit None) :: mk_implicits (n-1)
  in
  let rec mk_lambda_spine c namer = function
    | 0 -> c
    | n -> 
        Cic.Lambda 
          (namer n,
           (Cic.Implicit None), 
           mk_lambda_spine (CicSubstitution.lift 1 c) namer (n-1))
  in 
  let count_pis t arity = 
    let rec aux acc n = function
      | Cic.Prod (name,src,tgt) -> aux (acc@[name]) (n+1) tgt
      | _ -> n,acc
    in
    let len,names = aux [] 0 t in
    let len = len - arity in
    List.fold_left 
      (fun (n,l) x -> if n < len then n+1,l@[x] else n,l) (0,[]) 
      names
  in
  let compose c1 nc1 c2 nc2 =
   Cic.Appl ((*CicSubstitution.lift 1*) c2 :: mk_implicits (nc2 - sat2 - 1) @
     Cic.Appl ((*CicSubstitution.lift 1*) c1 :: mk_implicits nc1 ) ::
     mk_implicits sat2)
  in
  let rec create_subst_from_metas_to_rels n = function 
    | [] -> []
    | (metano, ctx, ty)::tl -> 
        (metano,(ctx,Cic.Rel n,ty)) ::
          create_subst_from_metas_to_rels (n-1) tl
  in
  let split_metasenv metasenv n =
    List.partition (fun (_,ctx,_) -> List.length ctx >= n) metasenv
  in
  let purge_unused_lambdas metasenv t =
    let rec aux = function
        | Cic.Lambda (_, Cic.Meta (i,_), t) when  
          List.exists (fun (j,_,_) -> j = i) metasenv ->
            aux (CicSubstitution.subst (Cic.Rel ~-100) t)
        | Cic.Lambda (name, s, t) -> 
            Cic.Lambda (name, s, aux t)
        | t -> t
    in
    aux t
  in
  let order_body_menv term body_metasenv c1_pis c2_pis =
    let rec purge_lambdas = function
      | Cic.Lambda (_,_,t) -> purge_lambdas t
      | t -> t
    in
    let skip_appl = function | Cic.Appl l -> List.tl l | _ -> assert false in
    let rec metas_of_term_and_types t =
      let metas = CicUtil.metas_of_term t in
      let types = 
       List.flatten       
        (List.map 
          (fun (i,_) -> try 
            let _,_,ty = CicUtil.lookup_meta i body_metasenv in metas_of_term_and_types ty
            with CicUtil.Meta_not_found _ -> []) 
          metas)
      in
      metas @ types
    in
    let sorted_metas_of_term world t = 
      let metas = metas_of_term_and_types t in
      (* this check should be useless *)
      let metas = List.filter (fun (i,_)->List.exists (fun (j,_,_) -> j=i) world) metas in
      let order_metas metasenv metas = 
        let module OT = struct type t = int let compare = Pervasives.compare end in
        let module S = HTopoSort.Make (OT) in
        let dep i = 
          try 
            let _,_,ty = List.find (fun (j,_,_) -> j=i) metasenv in
            let metas = List.map fst (CicUtil.metas_of_term ty) in
            HExtlib.list_uniq (List.sort Pervasives.compare metas)
          with Not_found -> []
        in
          S.topological_sort (List.map (fun (i,_) -> i) metas) dep 
      in 
      order_metas world metas
    in
    let metas_that_saturate l =
      List.fold_left 
        (fun (acc,n) t ->
          let metas = sorted_metas_of_term body_metasenv t in
          let metas = 
            List.filter (fun i -> List.for_all (fun (j,_) -> j<>i) acc) metas in
          let metas = List.map (fun i -> i,n) metas in
          metas @ acc, n+1)
        ([],0) l
    in
    let l_c2 = skip_appl (purge_lambdas term) in
    let l_c2_b,l_c2_a =
     try
      HExtlib.split_nth (c2_pis - sat2 - 1) l_c2
     with
      Failure _ -> assert false in
    let l_c1,l_c2_a =
     match l_c2_a with
        Cic.Appl (_::l_c1)::tl -> l_c1,tl
      | _ -> assert false in
    let meta_to_be_coerced =
     try
      match List.nth l_c1 (c1_pis - sat1 - 1) with
       | Cic.Meta (i,_) -> Some i
       | t -> 
          debug_print 
            (lazy("meta_to_be_coerced: " ^ CicPp.ppterm t));
          debug_print 
            (lazy("c1_pis: " ^ string_of_int c1_pis ^ 
             " sat1:" ^ string_of_int sat1));
          None
     with
      Failure _ -> assert false
    in
    (* BIG HACK ORRIBLE:
     * it should be (l_c2_b @ l_c1 @ l_c2_a), but in this case sym (eq_f) gets
     *  \A,B,f,x,y,Exy and not \B,A,f,x,y,Exy
     * as an orrible side effect, the other composites get a type lyke
     *  \A,x,y,Exy,B,f with 2 saturations
     *)
    let meta2no = fst (metas_that_saturate (l_c1 @ l_c2_b @ l_c2_a)) in
    let sorted =
     List.sort 
      (fun (i,ctx1,ty1) (j,ctx1,ty1) -> 
          try List.assoc i meta2no -  List.assoc j meta2no 
          with Not_found -> assert false) 
      body_metasenv
    in
    let rec position_of n acc =
     function
        [] -> assert false
      | (i,_,_)::_ when i = n -> acc
      | _::tl -> position_of n (acc + 1) tl
    in
    let saturations_res, position_of_meta_to_be_coerced = 
      match meta_to_be_coerced with
      | None -> 0,0
      | Some meta_to_be_coerced -> 
          debug_print
            (lazy ("META_TO_BE_COERCED: " ^ string_of_int meta_to_be_coerced));
          let position_of_meta_to_be_coerced =
            position_of meta_to_be_coerced 0 sorted in
          debug_print (lazy ("POSITION_OF_META_TO_BE_COERCED: " ^
            string_of_int position_of_meta_to_be_coerced));
          List.length sorted - position_of_meta_to_be_coerced - 1,
          position_of_meta_to_be_coerced
    in
    debug_print (lazy ("SATURATIONS: " ^ string_of_int saturations_res));
    sorted, saturations_res, position_of_meta_to_be_coerced
  in
  let namer l n = 
    let l = List.map (function Cic.Name s -> s | _ -> "A") l in
    let l = List.fold_left
      (fun acc s -> 
        let rec add' s =
          if List.exists ((=) s) acc then add' (s^"'") else s
        in
        acc@[add' s])
      [] l
    in
    let l = List.rev l in 
    Cic.Name (List.nth l (n-1))
  in 
  debug_print (lazy ("\nCOMPOSING"));
  debug_print (lazy (" c1= "^CicPp.ppterm c1 ^"  :  "^ CicPp.ppterm c1_ty));
  debug_print (lazy (" c2= "^CicPp.ppterm c2 ^"  :  "^ CicPp.ppterm c2_ty));
  let c1_pis, names_c1 = count_pis c1_ty arity1 in 
  let c2_pis, names_c2 = count_pis c2_ty arity2 in
  let c = compose c1 c1_pis c2 c2_pis in
  let spine_len = c1_pis + c2_pis in
  let c = mk_lambda_spine c (namer (names_c1 @ names_c2)) spine_len in
  debug_print (lazy ("COMPOSTA: " ^ CicPp.ppterm c));
  let old_insert_coercions = !CicRefine.insert_coercions in
  let old_pack_coercions = !CicRefine.pack_coercions in
  let c, metasenv, univ, saturationsres, cpos =
    try
      CicRefine.insert_coercions := false;
      CicRefine.pack_coercions := false;
      let term, ty, metasenv, ugraph = 
        CicRefine.type_of_aux' metasenv context c univ
      in
      debug_print(lazy("COMPOSED REFINED: "^CicPp.ppterm term));
      debug_print(lazy("COMPOSED REFINED (pretty): "^
        CicMetaSubst.ppterm_in_context [] ~metasenv term context));
(*       let metasenv = order_metasenv metasenv in *)
(*       debug_print(lazy("ORDERED MENV: "^CicMetaSubst.ppmetasenv [] metasenv)); *)
      let body_metasenv, lambdas_metasenv = 
        split_metasenv metasenv (spine_len + List.length context)
      in
      debug_print(lazy("B_MENV: "^CicMetaSubst.ppmetasenv [] body_metasenv));
      debug_print(lazy("L_MENV: "^CicMetaSubst.ppmetasenv [] lambdas_metasenv));
      let body_metasenv, saturationsres, cpos =
       order_body_menv term body_metasenv c1_pis c2_pis
      in
      debug_print(lazy("ORDERED_B_MENV: "^CicMetaSubst.ppmetasenv [] body_metasenv));
      let subst = create_subst_from_metas_to_rels spine_len body_metasenv in
      debug_print (lazy("SUBST: "^CicMetaSubst.ppsubst body_metasenv subst));
      let term = CicMetaSubst.apply_subst subst term in
      let metasenv = CicMetaSubst.apply_subst_metasenv subst metasenv in
      debug_print (lazy ("COMPOSED SUBSTITUTED: " ^ CicPp.ppterm term));
      let term, ty, metasenv, ugraph = 
        CicRefine.type_of_aux' metasenv context term ugraph
      in
      let body_metasenv, lambdas_metasenv = 
        split_metasenv metasenv (spine_len + List.length context)
      in
      let lambdas_metasenv = 
        List.filter 
          (fun (i,_,_) -> 
            List.for_all (fun (j,_,_) -> i <> j) original_metasenv)
          lambdas_metasenv
      in
      let term = purge_unused_lambdas lambdas_metasenv term in
      let metasenv = 
        List.filter 
          (fun (i,_,_) -> 
            List.for_all 
              (fun (j,_,_) ->
                i <> j || List.exists (fun (j,_,_) -> j=i) original_metasenv) 
              lambdas_metasenv) 
          metasenv 
      in
      debug_print (lazy ("####################"));
      debug_print (lazy ("COMPOSED: " ^ CicPp.ppterm term));
      debug_print (lazy ("SATURATIONS: " ^ string_of_int saturationsres));
      debug_print (lazy ("MENV: "^CicMetaSubst.ppmetasenv [] metasenv));
      debug_print (lazy ("####################"));
      CicRefine.insert_coercions := old_insert_coercions;
      CicRefine.pack_coercions := old_pack_coercions;
      term, metasenv, ugraph, saturationsres, cpos
    with
    | CicRefine.RefineFailure s 
    | CicRefine.Uncertain s -> debug_print s; 
        CicRefine.insert_coercions := old_insert_coercions;
        CicRefine.pack_coercions := old_pack_coercions;
        raise UnableToCompose
    | exn ->
        CicRefine.insert_coercions := old_insert_coercions;
        CicRefine.pack_coercions := old_pack_coercions;
        raise exn
  in
  let c_ty, univ = 
    CicTypeChecker.type_of_aux' ~subst:[] [] [] c univ
  in
  let real_composed = ref true in
  let c = 
    let rec is_id = function
      | Cic.Lambda(_,_,t) -> is_id t
      | Cic.Rel 1 -> true
      | _ -> false
    in
    let is_id = function
      | Cic.Const (u,_) -> 
          (match CicEnvironment.get_obj CicUniv.empty_ugraph u with
          | Cic.Constant (_,Some bo,_,_,_), _ ->  is_id bo
          | _ -> false)
      | _ -> false
    in
    let unvariant u =
     match CicEnvironment.get_obj CicUniv.empty_ugraph u with
     | Cic.Constant (_,Some (Cic.Const (u',_)),_,_,attrs), _
       when List.exists ((=) (`Flavour `Variant)) attrs ->
         u'
     | _ -> u
    in
    let is_variant u =
     match CicEnvironment.get_obj CicUniv.empty_ugraph u with
     | Cic.Constant (_,Some (Cic.Const (u',_)),_,_,attrs), _
       when List.exists ((=) (`Flavour `Variant)) attrs -> true
     | _ -> false
    in
    let rec aux = function
      | Cic.Lambda(n,s,t) -> Cic.Lambda(n,s,aux t)
      | Cic.Appl (c::_) as t -> 
          let t = 
            if is_id c then
              (real_composed := false ;
               CicReduction.head_beta_reduce ~delta:true t)
            else t
          in 
          (match t with
          | Cic.Appl l -> Cic.Appl (List.map aux l)
          | Cic.Const (u,[]) when is_variant u -> Cic.Const (unvariant u,[])
          | t -> t)
       | Cic.Const (u,[]) when is_variant u -> Cic.Const (unvariant u,[])
       | t -> t
    in
    let simple_eta_c t = 
      let incr = 
        List.map (function Cic.Rel n -> Cic.Rel (n+1) | _ -> assert false)
      in
      let rec aux acc ctx = function
        | Cic.Lambda (n,s,tgt) -> 
            aux (incr acc @ [Cic.Rel 1]) (Some (n,Cic.Decl s) ::ctx) tgt
        | Cic.Appl (t::tl) when tl = acc && 
            CicTypeChecker.does_not_occur ctx 0 (List.length acc) t -> true, t
        | t -> false, t
      in
      let b, newt = aux [] [] t in
      if b then newt else t
    in
     simple_eta_c (aux c)
  in
  debug_print (lazy ("COMPOSED COMPRESSED: " ^ string_of_bool !real_composed ^" : " ^ CicPp.ppterm c));
  c, c_ty, metasenv, univ, saturationsres, arity2, cpos, !real_composed
;;

let build_obj c c_ty univ arity is_var =
  let cleaned_ty =
    FreshNamesGenerator.clean_dummy_dependent_types c_ty 
  in
  let obj = Cic.Constant ("xxxx",Some c,cleaned_ty,[],
    [`Generated] @ if not is_var then [`Flavour `Variant] else [] )  in 

    obj,univ
;;

(* removes from l the coercions that are in !coercions *)
let filter_duplicates l coercions =
  List.filter (
   fun (src,l1,tgt) ->
     not (List.exists (fun (s,t,l2) -> 
       CoercDb.eq_carr s src && 
       CoercDb.eq_carr t tgt &&
       try 
         List.for_all2 (fun (u1,_,_) (u2,_,_) -> UriManager.eq u1 u2) l1 l2
       with
       | Invalid_argument "List.for_all2" -> 
           debug_print (lazy("XXX")); false)
     coercions))
  l
;;

let mangle s t l = 
  (*List.fold_left
    (fun s x -> s ^ "_" ^ x)
    (s ^ "_OF_" ^ t ^ "_BY" ^ string_of_int (List.length l)) l*)
  s ^ "_OF_" ^ t
;;

exception ManglingFailed of string 

let number_if_already_defined buri name l =
  let err () =
    raise 
      (ManglingFailed 
        ("Unable to give an altenative name to " ^ buri ^ "/" ^ name ^ ".con"))
  in
  let rec aux n =
    let suffix = if n > 0 then ("__" ^ string_of_int n) else "" in
    let suri = buri ^ "/" ^ name ^ suffix ^ ".con" in
    let uri = UriManager.uri_of_string suri in
    let retry () = if n < max_int then aux (n+1) else err () in
    if List.exists (UriManager.eq uri) l then retry ()
    else
      try
        let _  = Http_getter.resolve' ~local:true ~writable:true uri in
        if Http_getter.exists' ~local:true uri then retry () else uri
      with 
      | Http_getter_types.Key_not_found _ -> uri
      | Http_getter_types.Unresolvable_URI _ -> assert false
  in
  aux 0
;;
  
(* given a new coercion uri from src to tgt returns 
 * a list of (new coercion uri, coercion obj, universe graph) 
 *)
let close_coercion_graph src tgt uri saturations baseuri =
  (* check if the coercion already exists *)
  let coercions = CoercDb.to_list (CoercDb.dump ()) in
  let todo_list = get_closure_coercions src tgt (uri,saturations,0) coercions in
  debug_print (lazy("composed " ^ string_of_int (List.length todo_list)));
  let todo_list = filter_duplicates todo_list coercions in
  try
    let new_coercions = 
      List.fold_left 
        (fun acc (src, l , tgt) ->
          try 
            match l with
            | [] -> assert false 
            | (he,saturations1,arity1) :: tl ->
                let first_step = 
                  Cic.Constant ("", Some (CicUtil.term_of_uri he),
                  Cic.Sort Cic.Prop, [], [`Generated]),
                  saturations1,
                  arity1,0
                in
                let o,_ = 
                  List.fold_left (fun (o,univ) (coer,saturations2,arity2) ->
                    match o with 
                    | Cic.Constant (_,Some u,_,[],_),saturations1,arity1,_ ->
                        let t, t_ty, menv, univ, saturationsres, 
                          arityres, cposres, is_var 
                        = 
                          generate_composite' (u,saturations1,arity1) 
                            (CicUtil.term_of_uri coer,
                             saturations2, arity2) [] [] univ
                        in
                        if (menv <> []) then
                          HLog.warn "MENV non empty after composing coercions";
                        let o,univ = build_obj t t_ty univ arityres is_var in
                         (o,saturationsres,arityres,cposres),univ
                    | _ -> assert false 
                  ) (first_step, CicUniv.oblivion_ugraph) tl
                in
                let name_src = CoercDb.string_of_carr src in
                let name_tgt = CoercDb.string_of_carr tgt in
                let by = List.map (fun u,_,_ -> UriManager.name_of_uri u) l in
                let name = mangle name_tgt name_src by in
                let c_uri = 
                  number_if_already_defined baseuri name 
                    (List.map (fun (_,_,u,_,_,_,_) -> u) acc) 
                in
                let named_obj,saturations,arity,cpos = 
                  match o with
                  | Cic.Constant (_,bo,ty,vl,attrs),saturations,arity,cpos ->
                      Cic.Constant (name,bo,ty,vl,attrs),saturations,arity,cpos
                  | _ -> assert false 
                in
                  (src,tgt,c_uri,saturations,named_obj,arity,cpos)::acc
          with UnableToCompose -> acc
      ) [] todo_list
    in
    new_coercions
  with ManglingFailed s -> HLog.error s; []
;;

CicCoercion.set_close_coercion_graph close_coercion_graph;;

(* generate_composite (c2 (c1 s)) in the universe graph univ
 * both living in the same context and metasenv *)
let generate_composite c1 c2 context metasenv univ sat1 sat2 =
 let a,_,b,c,_,_,_,_ =
  generate_composite' (c1,sat1,0) (c2,sat2,0) context metasenv univ
 in
  a,b,c
;;

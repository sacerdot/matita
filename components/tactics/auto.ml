(* Copyright (C) 2002, HELM Team.
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
 * http://cs.unibo.it/helm/.
 *)

open AutoTypes;;
open AutoCache;;

let debug = false;;
let debug_print s = 
  if debug then prerr_endline (Lazy.force s);;


let mk_irl ctx = CicMkImplicit.identity_relocation_list_for_metavariable ctx;;
let ugraph = CicUniv.oblivion_ugraph;;
let typeof = CicTypeChecker.type_of_aux';;
let ppterm ctx t = 
  let names = List.map (function None -> None | Some (x,_) -> Some x) ctx in
  CicPp.pp t names
;;

let is_propositional context sort = 
  match CicReduction.whd context sort with
  | Cic.Sort Cic.Prop 
  | Cic.Sort (Cic.CProp _) -> true
  | _-> false
;;

let is_in_prop context subst metasenv ty =
  let sort,u = typeof ~subst metasenv context ty CicUniv.oblivion_ugraph in
  is_propositional context sort
;;

exception NotConvertible;;

let check_proof_is_valid proof metasenv context goalty =
  if debug then
    begin
      try
	let ty,u = typeof metasenv context proof CicUniv.oblivion_ugraph in
	let b,_ = CicReduction.are_convertible context ty goalty u in
	if not b then raise NotConvertible else b
      with _ ->
        let names = 
          List.map (function None -> None | Some (x,_) -> Some x) context 
        in
          debug_print (lazy ("PROOF:" ^ CicPp.pp proof names));
          (* debug_print (lazy ("PROOFTY:" ^ CicPp.pp ty names)); *)
          debug_print (lazy ("GOAL:" ^ CicPp.pp goalty names));
          debug_print (lazy ("MENV:" ^ CicMetaSubst.ppmetasenv [] metasenv));
        false
    end
  else true
;;

let assert_proof_is_valid proof metasenv context goalty =
  assert (check_proof_is_valid proof metasenv context goalty)
;;

let assert_subst_are_disjoint subst subst' =
  if debug then
    assert(List.for_all
             (fun (i,_) -> List.for_all (fun (j,_) -> i<>j) subst') 
             subst)
  else ()
;;

let split_goals_in_prop metasenv subst gl =
  List.partition 
    (fun g ->
      let _,context,ty = CicUtil.lookup_meta g metasenv in
      try
        let sort,u = typeof ~subst metasenv context ty ugraph in
        is_propositional context sort
      with 
      | CicTypeChecker.AssertFailure s 
      | CicTypeChecker.TypeCheckerFailure s -> 
          debug_print 
            (lazy ("NON TIPA" ^ ppterm context (CicMetaSubst.apply_subst subst ty)));
          debug_print s;
          false)
    (* FIXME... they should type! *)
    gl
;;

let split_goals_with_metas metasenv subst gl =
  List.partition 
    (fun g ->
      let _,context,ty = CicUtil.lookup_meta g metasenv in
      let ty = CicMetaSubst.apply_subst subst ty in
      CicUtil.is_meta_closed ty)
    gl
;;

let order_new_goals metasenv subst open_goals ppterm =
  let prop,rest = split_goals_in_prop metasenv subst open_goals in
  let closed_prop, open_prop = split_goals_with_metas metasenv subst prop in
  let closed_type, open_type = split_goals_with_metas metasenv subst rest in
  let open_goals =
    (List.map (fun x -> x,P) (open_prop @ closed_prop)) 
    @ 
    (List.map (fun x -> x,T) (open_type @ closed_type))
  in
  let tys = 
    List.map 
      (fun (i,sort) -> 
        let _,_,ty = CicUtil.lookup_meta i metasenv in i,ty,sort) open_goals 
  in
  debug_print (lazy ("   OPEN: "^
    String.concat "\n" 
      (List.map 
         (function
            | (i,t,P) -> string_of_int i   ^ ":"^ppterm t^ "Prop" 
            | (i,t,T) -> string_of_int i  ^ ":"^ppterm t^ "Type")
         tys)));
  open_goals
;;

let is_an_equational_goal = function
  | Cic.Appl [Cic.MutInd(u,_,_);_;_;_] when LibraryObjects.is_eq_URI u -> true
  | _ -> false
;;

type auto_params = Cic.term list option * (string * string) list 

let elems = ref [] ;;

(* closing a term w.r.t. its metavariables
   very naif version: it does not take dependencies properly into account *)

let naif_closure ?(prefix_name="xxx_") t metasenv context =
  let in_term t (i,_,_) =
    List.exists (fun (j,_) -> j=i) (CicUtil.metas_of_term t)
  in
  let metasenv = List.filter (in_term t) metasenv in
  let metasenv = ProofEngineHelpers.sort_metasenv metasenv in
  let n = List.length metasenv in
  let what = List.map (fun (i,cc,ty) -> Cic.Meta(i,[])) metasenv in
  let _,with_what =
    List.fold_left
      (fun (i,acc) (_,cc,ty) -> (i-1,Cic.Rel i::acc)) 
      (n,[]) metasenv 
  in
  let t = CicSubstitution.lift n t in
  let body =
    ProofEngineReduction.replace_lifting 
      ~equality:(fun c t1 t2 ->
         match t1,t2 with
         | Cic.Meta(i,_),Cic.Meta(j,_) -> i = j
         | _ -> false) 
      ~context ~what ~with_what ~where:t 
  in
  let _, t =
    List.fold_left
      (fun (n,t) (_,cc,ty) -> 
        n-1, Cic.Lambda(Cic.Name (prefix_name^string_of_int n),
               CicSubstitution.lift n ty,t))
      (n-1,body) metasenv 
  in
  t, List.length metasenv
;;

let lambda_close ?prefix_name t menv ctx =
  let t, num_lambdas = naif_closure ?prefix_name t menv ctx in
    List.fold_left
      (fun (t,i) -> function 
        | None -> CicSubstitution.subst (Cic.Implicit None) t,i (* delift *)
        | Some (name, Cic.Decl ty) -> Cic.Lambda (name, ty, t),i+1
        | Some (name, Cic.Def (bo, ty)) -> Cic.LetIn (name, bo, ty, t),i+1)
      (t,num_lambdas) ctx
;;
  
(* functions for retrieving theorems *)


exception FillingFailure of AutoCache.cache * AutomationCache.tables

let rec unfold context = function
  | Cic.Prod(name,s,t) -> 
      let t' = unfold ((Some (name,Cic.Decl s))::context) t in
        Cic.Prod(name,s,t')        
  | t -> ProofEngineReduction.unfold context t

let find_library_theorems dbd proof goal = 
  let univ = MetadataQuery.universe_of_goal ~dbd false proof goal in
  let terms = List.map CicUtil.term_of_uri univ in
  List.map 
    (fun t -> 
       (t,fst(CicTypeChecker.type_of_aux' [] [] t CicUniv.oblivion_ugraph))) 
    terms

let find_context_theorems context metasenv =
  let l,_ =
    List.fold_left
      (fun (res,i) ctxentry ->
         match ctxentry with
           | Some (_,Cic.Decl t) -> 
               (Cic.Rel i, CicSubstitution.lift i t)::res,i+1
           | Some (_,Cic.Def (_,t)) ->
               (Cic.Rel i, CicSubstitution.lift i t)::res,i+1
           | None -> res,i+1)
      ([],1) context
  in l

let rec is_an_equality = function
  | Cic.Appl [Cic.MutInd (uri, _, _); _; _; _] 
    when (LibraryObjects.is_eq_URI uri) -> true
  | Cic.Prod (_, _, t) -> is_an_equality t
  | _ -> false
;;

let partition_equalities =
  List.partition (fun (_,ty) -> is_an_equality ty)


let default_auto tables _ cache _ _ _ _ = [],cache,tables ;; 

(* giusto per provare che succede 
let is_unit_equation context metasenv oldnewmeta term =
  let head, metasenv, args, newmeta =
    TermUtil.saturate_term oldnewmeta metasenv context term 0
  in
  let newmetas = 
    List.filter (fun (i,_,_) -> i >= oldnewmeta) metasenv 
  in
    Some (args,metasenv,newmetas,head,newmeta) *)

let is_unit_equation context metasenv oldnewmeta term = 
  let head, metasenv, args, newmeta =
    TermUtil.saturate_term oldnewmeta metasenv context term 0
  in
  let propositional_args = 
    HExtlib.filter_map
      (function 
      | Cic.Meta(i,_) -> 
          let _,_,mt = CicUtil.lookup_meta i metasenv in
          let sort,u = 
            CicTypeChecker.type_of_aux' metasenv context mt 
              CicUniv.oblivion_ugraph
          in
          if is_propositional context sort then Some i else None 
      | _ -> assert false)
    args
  in
    if propositional_args = [] then 
      let newmetas = 
        List.filter (fun (i,_,_) -> i >= oldnewmeta) metasenv 
      in
        Some (args,metasenv,newmetas,head,newmeta)
    else None
;;

let get_candidates skip_trie_filtering universe cache t =
  let t = if skip_trie_filtering then Cic.Meta(0,[]) else t in
  let candidates= 
    (Universe.get_candidates universe t)@(AutoCache.get_candidates cache t)
  in 
  let debug_msg =
    (lazy ("candidates for " ^ (CicPp.ppterm t) ^ " = " ^ 
             (String.concat "\n" (List.map CicPp.ppterm candidates)))) in
  debug_print debug_msg;
  candidates
;;

let only signature context metasenv t =
  try
    let ty,_ = 
      CicTypeChecker.type_of_aux' metasenv context t CicUniv.oblivion_ugraph 
    in
    let consts = MetadataConstraints.constants_of ty in
    let b = MetadataConstraints.UriManagerSet.subset consts signature in
(*     if b then (prerr_endline ("keeping " ^ (CicPp.ppterm t)); b)  *)
    if b then b 
    else
      let ty' = unfold context ty in
      let consts' = MetadataConstraints.constants_of ty' in
      let b = MetadataConstraints.UriManagerSet.subset consts' signature  in
(*
	if not b then prerr_endline ("filtering " ^ (CicPp.ppterm t))
	else prerr_endline ("keeping " ^ (CicPp.ppterm t)); 
*)
      b
  with 
  | CicTypeChecker.TypeCheckerFailure _ -> assert false
  | ProofEngineTypes.Fail _ -> false (* unfold may fail *)
;;

let not_default_eq_term t =
  try
    let uri = CicUtil.uri_of_term t in
      not (LibraryObjects.in_eq_URIs uri)
  with Invalid_argument _ -> true

let retrieve_equations dont_filter signature universe cache context metasenv =
  match LibraryObjects.eq_URI() with
    | None -> [] 
    | Some eq_uri -> 
        let eq_uri = UriManager.strip_xpointer eq_uri in
        let fake= Cic.Meta(-1,[]) in
        let fake_eq = Cic.Appl [Cic.MutInd (eq_uri,0, []);fake;fake;fake] in
        let candidates = get_candidates false universe cache fake_eq in
        if dont_filter then candidates
        else let eq_uri = UriManager.uri_of_uriref eq_uri 0 None in
          (* let candidates = List.filter not_default_eq_term candidates in *)
          List.filter 
	    (only (MetadataConstraints.UriManagerSet.add eq_uri signature) 
	       context metasenv) candidates 

let build_equality bag head args proof newmetas = 
  match head with
  | Cic.Appl [Cic.MutInd (uri, _, _); ty; t1; t2] ->
      let p =
        if args = [] then proof else Cic.Appl (proof::args)
      in 
      let o = !Utils.compare_terms t1 t2 in
      let stat = (ty,t1,t2,o) in
      (* let w = compute_equality_weight stat in *)
      let w = 0 in 
      let proof = Equality.Exact p in
      let bag, e = Equality.mk_equality bag (w, proof, stat, newmetas) in
      (* to clean the local context of metas *)
      Equality.fix_metas bag e
  | _ -> assert false
;;

let partition_unit_equalities context metasenv newmeta bag equations =
  List.fold_left
    (fun (bag,units,other,maxmeta)(t,ty) ->
       if not (CicUtil.is_meta_closed t && CicUtil.is_meta_closed ty) then
         let _ = 
           HLog.warn 
           ("Skipping " ^ CicMetaSubst.ppterm_in_context ~metasenv [] t context
             ^ " since it is not meta closed")
         in
         bag, units,(t,ty)::other,maxmeta
       else
       match is_unit_equation context metasenv maxmeta ty with
         | Some (args,metasenv,newmetas,head,newmeta') ->
             let bag, equality =
               build_equality bag head args t newmetas in
             bag, equality::units,other,maxmeta
         | None -> 
             bag, units,(t,ty)::other,maxmeta)
    (bag,[],[],newmeta) equations
;;

let init_cache_and_tables 
  ?dbd ~use_library ~use_context 
  automation_cache restricted_univ (proof, goal) 
=
  let _, metasenv, subst, _, _, _ = proof in
  let _,context,_ = CicUtil.lookup_meta goal metasenv in
  let add_list_to_tables metasenv subst automation_cache ct =
    List.fold_left 
      (fun automation_cache (t,_) -> 
          AutomationCache.add_term_to_active automation_cache
           metasenv subst context t None)
      automation_cache ct
  in
  match restricted_univ with
    | None ->
	let ct = 
	  if use_context then find_context_theorems context metasenv else [] 
	in
	let lt = 
	  match use_library, dbd with
	    | true, Some dbd -> find_library_theorems dbd metasenv goal 
	    | _ -> []
	in
	let cache = AutoCache.cache_empty in
	let cache = cache_add_list cache context (ct@lt) in  
	let automation_cache = 
	  add_list_to_tables metasenv subst automation_cache ct 
	in
(*     AutomationCache.pp_cache automation_cache; *)
	  automation_cache.AutomationCache.univ, 
	automation_cache.AutomationCache.tables, 
	cache
    | Some restricted_univ ->
	let t_ty = 
	  List.map
            (fun  t ->
               let ty, _ = CicTypeChecker.type_of_aux' 
		 metasenv ~subst:[] context t CicUniv.oblivion_ugraph
               in
		 t, ty)
            restricted_univ
	in
	  (* let automation_cache = AutomationCache.empty () in *) 
	let automation_cache = 
	  let universe = Universe.empty in
	  let universe = 
            Universe.index_list universe context t_ty
	  in
	    { automation_cache with AutomationCache.univ = universe }
	in
	let ct = 
	  if use_context then find_context_theorems context metasenv else t_ty
	in
	let automation_cache = 
	  add_list_to_tables metasenv subst automation_cache ct
	in
    (* AutomationCache.pp_cache automation_cache; *)
	  automation_cache.AutomationCache.univ, 
	automation_cache.AutomationCache.tables, 
	cache_empty
;;

let fill_hypothesis context metasenv subst term tables (universe:Universe.universe) cache auto fast = 
  let actives, passives, bag = tables in 
  let bag, head, metasenv, args = 
    Equality.saturate_term bag metasenv subst context term 
  in
  let tables = actives, passives, bag in 
  let propositional_args = 
    HExtlib.filter_map
      (function 
      | Cic.Meta(i,_) -> 
          let _,_,mt = CicUtil.lookup_meta i metasenv in
          let sort,u = 
            CicTypeChecker.type_of_aux' metasenv context mt 
              CicUniv.oblivion_ugraph
          in
          if is_propositional context sort then Some i else None 
      | _ -> assert false)
    args
  in
  let results,cache,tables = 
    if propositional_args = [] then 
      let _,_,bag = tables in
      let newmetas = Equality.filter_metasenv_gt_maxmeta bag metasenv in
      [args,metasenv,newmetas,head],cache,tables
    else
      (*
      let proof = 
        None,metasenv,term,term (* term non e' significativo *)
      in *)
      let flags = 
        if fast then
          {AutoTypes.default_flags() with 
           AutoTypes.timeout = Unix.gettimeofday() +. 1.0;
           maxwidth = 2;maxdepth = 2;
           use_paramod=true;use_only_paramod=false}
        else
          {AutoTypes.default_flags() with
           AutoTypes.timeout = Unix.gettimeofday() +. 1.0;
           maxwidth = 2;maxdepth = 4;
           use_paramod=true;use_only_paramod=false} 
      in
      match auto tables universe cache context metasenv propositional_args flags with
      | [],cache,tables -> raise (FillingFailure (cache,tables))
      | substs,cache,tables ->
          let actives, passaives, bag = tables in 
          let bag, res = 
          List.fold_right 
            (fun subst (bag,acc) ->
              let metasenv = 
                CicMetaSubst.apply_subst_metasenv subst metasenv
              in
              let head = CicMetaSubst.apply_subst subst head in
              let newmetas = Equality.filter_metasenv_gt_maxmeta bag metasenv in
              let args = List.map (CicMetaSubst.apply_subst subst) args in
              let newm = CicMkImplicit.new_meta metasenv subst in
              let bag = Equality.push_maxmeta bag newm in
              bag, ((args,metasenv,newmetas,head) :: acc))
            substs (bag,[])
          in
          let tables = actives, passives, bag in 
           res, cache, tables
  in
  results,cache,tables
;;

let build_equalities auto context metasenv subst tables universe cache equations =
  List.fold_left 
    (fun (tables,facts,cache) (t,ty) ->
       (* in any case we add the equation to the cache *)
       let cache = AutoCache.cache_add_list cache context [(t,ty)] in
       try
         let saturated, cache, tables = 
           fill_hypothesis context metasenv subst ty tables universe cache auto true
         in
         let eqs, tables = 
           List.fold_left 
             (fun (acc, tables) (args,metasenv,newmetas,head) ->
                let actives, passives, bag = tables in 
                let bag, equality =
                  build_equality bag head args t newmetas 
                in
                let tables = actives, passives, bag in
                  equality::acc,tables)
             ([],tables) saturated
         in
           (tables, eqs@facts, cache)
       with FillingFailure (cache,tables) ->
         (* if filling hypothesis fails we add the equation to
            the cache *)
         (tables,facts,cache)
      )
    (tables,[],cache) equations

let close_more tables context status auto signature universe cache =
  let proof, goalno = status in
  let _, metasenv,subst,_,_, _ = proof in  
  let equations = 
    retrieve_equations false signature universe cache context metasenv 
  in
  let eqs_and_types =
    HExtlib.filter_map 
      (fun t -> 
         let ty,_ =
           CicTypeChecker.type_of_aux' metasenv context t
           CicUniv.oblivion_ugraph in
           (* retrieve_equations could also return flexible terms *)
           if is_an_equality ty then Some(t,ty) else None)
      equations in
  let tables, units, cache = 
    build_equalities auto context metasenv subst tables universe cache eqs_and_types 
  in
  let active,passive,bag = tables in
  let passive = Saturation.add_to_passive units passive in
  let no = List.length units in
  let active, passive, bag = 
    Saturation.pump_actives context bag active passive (no+1) infinity
  in 
    (active,passive,bag), cache
;;

let find_context_equalities dbd tables context proof (universe:Universe.universe) cache 
=
  let module C = Cic in
  let module S = CicSubstitution in
  let module T = CicTypeChecker in
  let _,metasenv,subst,_,_, _ = proof in
  (* if use_auto is true, we try to close the hypothesis of equational
    statements using auto; a naif, and probably wrong approach *)
  let rec aux tables cache index = function
    | [] -> tables, [], cache
    | (Some (_, C.Decl (term)))::tl ->
        debug_print
          (lazy
             (Printf.sprintf "Examining: %d (%s)" index (CicPp.ppterm term)));
        let do_find tables context term =
          match term with
          | C.Prod (name, s, t) when is_an_equality t ->
              (try 
                let term = S.lift index term in
                let saturated, cache, tables = 
                  fill_hypothesis context metasenv subst term 
                    tables universe cache default_auto false
                in
                let actives, passives, bag = tables in 
                let bag,eqs = 
                  List.fold_left 
                   (fun (bag,acc) (args,metasenv,newmetas,head) ->
                     let bag, equality = 
                       build_equality bag head args (Cic.Rel index) newmetas 
                     in
                     bag, equality::acc)
                   (bag,[]) saturated
                in
                let tables = actives, passives, bag in
                 tables, eqs, cache
              with FillingFailure (cache,tables) ->
                tables, [], cache)
          | C.Appl [C.MutInd (uri, _, _); ty; t1; t2]
              when LibraryObjects.is_eq_URI uri ->
              let term = S.lift index term in
              let actives, passives, bag = tables in 
              let bag, e = 
                build_equality bag term [] (Cic.Rel index) [] 
              in
              let tables = actives, passives, bag in
              tables, [e], cache
          | _ -> tables, [], cache
        in 
        let tables, eqs, cache = do_find tables context term in
        let tables, rest, cache = aux tables cache (index+1) tl in
        tables, List.map (fun x -> index,x) eqs @ rest, cache
    | _::tl ->
        aux tables cache (index+1) tl
  in
  let tables, il, cache = aux tables cache 1 context in
  let indexes, equalities = List.split il in
  tables, indexes, equalities, cache
;;

(********** PARAMETERS PASSING ***************)

let bool params name default =
    try 
      let s = List.assoc name params in 
      if s = "" || s = "1" || s = "true" || s = "yes" || s = "on" then true
      else if s = "0" || s = "false" || s = "no" || s= "off" then false
      else 
        let msg = "Unrecognized value for parameter "^name^"\n" in
        let msg = msg^"Accepted values are 1,true,yes,on and 0,false,no,off" in
        raise (ProofEngineTypes.Fail (lazy msg))
    with Not_found -> default
;; 

let string params name default =
    try List.assoc name params with
    | Not_found -> default
;; 

let int params name default =
    try int_of_string (List.assoc name params) with
    | Not_found -> default
    | Failure _ -> 
        raise (ProofEngineTypes.Fail (lazy (name ^ " must be an integer")))
;;  

let flags_of_params params ?(for_applyS=false) () =
 let int = int params in
 let bool = bool params in
 let close_more = bool "close_more" false in
 let use_paramod = bool "use_paramod" true in
 let skip_trie_filtering = bool "skip_trie_filtering" false in
 let skip_context = bool "skip_context" false in
 let use_only_paramod =
  if for_applyS then true else bool "paramodulation" false in
 let use_library = bool "library"  
   ((AutoTypes.default_flags()).AutoTypes.use_library) in
 let depth = int "depth" ((AutoTypes.default_flags()).AutoTypes.maxdepth) in
 let width = int "width" ((AutoTypes.default_flags()).AutoTypes.maxwidth) in
 let size = int "size" ((AutoTypes.default_flags()).AutoTypes.maxsize) in
 let gsize = int "gsize" ((AutoTypes.default_flags()).AutoTypes.maxgoalsizefactor) in
 let do_type = bool "type" false in
 let timeout = int "timeout" 0 in
  { AutoTypes.maxdepth = 
      if use_only_paramod then 2 else depth;
    AutoTypes.maxwidth = width;
    AutoTypes.maxsize = size;
    AutoTypes.timeout = 
      if timeout = 0 then
       if for_applyS then Unix.gettimeofday () +. 30.0
       else
         infinity
      else
       Unix.gettimeofday() +. (float_of_int timeout);
    AutoTypes.use_library = use_library; 
    AutoTypes.use_paramod = use_paramod;
    AutoTypes.use_only_paramod = use_only_paramod;
    AutoTypes.close_more = close_more;
    AutoTypes.dont_cache_failures = false;
    AutoTypes.maxgoalsizefactor = gsize;
    AutoTypes.do_types = do_type;
    AutoTypes.skip_trie_filtering = skip_trie_filtering;
    AutoTypes.skip_context = skip_context;
  }


let eq_of_goal = function
  | Cic.Appl [Cic.MutInd(uri,0,_);_;_;_] when LibraryObjects.is_eq_URI uri ->
      uri
  | _ -> raise (ProofEngineTypes.Fail (lazy ("The goal is not an equality ")))
;;

(* performs steps of rewrite with the universe, obtaining if possible 
 * a trivial goal *)
let solve_rewrite ~automation_cache ~params:(univ,params) (proof,goal)= 
  let steps = int_of_string (string params "steps" "4") in 
  let use_context = bool params "use_context" true in 
  let universe, tables, cache =
   init_cache_and_tables ~use_library:false ~use_context
     automation_cache univ (proof,goal) 
  in
  let actives, passives, bag = tables in 
  let pa,metasenv,subst,pb,pc,pd = proof in
  let _,context,ty = CicUtil.lookup_meta goal metasenv in
  let metasenv = CicMetaSubst.apply_subst_metasenv subst metasenv in
  let context = CicMetaSubst.apply_subst_context subst context in
  let ty = CicMetaSubst.apply_subst subst ty in
  let eq_uri = eq_of_goal ty in
  let initgoal = [], metasenv, ty in
  let table = 
    let equalities = (Saturation.list_of_passive passives) in
    List.fold_left (fun tbl eq -> Indexing.index tbl eq) (snd actives) equalities
  in
  let env = metasenv,context,CicUniv.oblivion_ugraph in
  debug_print (lazy ("demod to solve: " ^ CicPp.ppterm ty));
  match Indexing.solve_demodulating bag env table initgoal steps with 
  | Some (bag, gproof, metasenv, sub_subst, proof) ->
      let subst_candidates,extra_infos = 
        List.split 
          (HExtlib.filter_map 
             (fun (i,c,_) -> 
                if i <> goal && c = context then Some (i,(c,ty)) else None) 
             metasenv)
      in
      let proofterm,proto_subst = 
        let proof = Equality.add_subst sub_subst proof in
        Equality.build_goal_proof 
          bag eq_uri gproof proof ty subst_candidates context metasenv
      in
      let proofterm = Subst.apply_subst sub_subst proofterm in
      let extrasubst = 
        HExtlib.filter_map
          (fun (i,((c,ty),t)) -> 
             match t with
             | Cic.Meta (j,_) when i=j -> None
             | _ -> Some (i,(c,t,ty)))
          (List.combine subst_candidates 
            (List.combine extra_infos proto_subst))
      in
      let subst = subst @ extrasubst in
      let metasenv = CicMetaSubst.apply_subst_metasenv subst metasenv in
      let proofterm, _, metasenv,subst, _ =
        CicRefine.type_of metasenv subst context proofterm
          CicUniv.oblivion_ugraph
      in
      let status = (pa,metasenv,subst,pb,pc,pd), goal in
      ProofEngineTypes.apply_tactic 
        (PrimitiveTactics.apply_tac ~term:proofterm) status
  | None -> 
      raise 
        (ProofEngineTypes.Fail (lazy 
          ("Unable to solve with " ^ string_of_int steps ^ " demodulations")))
;;

(* Demodulate thorem *)
let open_type ty bo =
  let rec open_type_aux context ty k args =
    match ty with 
      | Cic.Prod (n,s,t) ->
	  let n' = 
	    FreshNamesGenerator.mk_fresh_name [] context n ~typ:s ~subst:[] in
          let entry = match n' with
	    | Cic.Name _    -> Some (n',(Cic.Decl s))
	    | Cic.Anonymous -> None
	  in
	    open_type_aux (entry::context) t (k+1) ((Cic.Rel k)::args)
      | Cic.LetIn (n,s,sty,t) ->
          let entry = Some (n,(Cic.Def (s,sty)))
	  in
	    open_type_aux (entry::context) t (k+1) args
      | _  -> context, ty, args
  in
  let context, ty, args = open_type_aux [] ty 1 [] in
  match args with
    | [] -> context, ty, bo
    | _ -> context, ty, Cic.Appl (bo::args)
;; 

let rec close_type bo ty context =
  match context with 
    | [] -> assert_proof_is_valid bo [] [] ty; (bo,ty)
    | Some (n,(Cic.Decl s))::tl ->
	close_type (Cic.Lambda (n,s,bo)) (Cic.Prod (n,s,ty)) tl
    | Some (n,(Cic.Def (s,sty)))::tl ->
	close_type (Cic.LetIn (n,s,sty,bo)) (Cic.LetIn (n,s,sty,ty)) tl
    | _ -> assert false
;; 

let is_subsumed univ context ty =
  let candidates = Universe.get_candidates univ ty in
    List.fold_left 
      (fun res cand ->
	 match res with
	   | Some found -> Some found
	   | None -> 
	       try 
                 let mk_irl = 
                   CicMkImplicit.identity_relocation_list_for_metavariable in
		 let metasenv = [(0,context,ty)] in
		 let fake_proof = 
                   None,metasenv,[] , (lazy (Cic.Meta(0,mk_irl context))),ty,[]
                 in
		 let (_,metasenv,subst,_,_,_), open_goals =
                   ProofEngineTypes.apply_tactic 
                     (PrimitiveTactics.apply_tac ~term:cand) 
                     (fake_proof,0)
		 in
                 let prop_goals, other = 
                   split_goals_in_prop metasenv subst open_goals 
                 in
		  if prop_goals = [] then Some cand else None
	       with 
		 | ProofEngineTypes.Fail s -> None
		 | CicUnification.Uncertain s ->  None
      ) None candidates
;;

let demodulate_theorem ~automation_cache uri =
  let eq_uri = 
    match LibraryObjects.eq_URI () with
      | Some (uri) -> uri
      | None -> raise (ProofEngineTypes.Fail (lazy "equality not declared")) in
  let obj,_ = CicEnvironment.get_cooked_obj CicUniv.empty_ugraph uri
  in
  let context,ty,bo =
    match obj with 
      | Cic.Constant(n, _, ty ,_, _) -> open_type ty (Cic.Const(uri,[]))
      | _ -> raise (ProofEngineTypes.Fail (lazy "not a theorem"))
  in
  if CicUtil.is_closed ty then 
    raise (ProofEngineTypes.Fail (lazy ("closed term: dangerous reduction")));
  let initgoal = [], [], ty in
  (* compute the signature *)
  let signature = 
    let ty_set = MetadataConstraints.constants_of ty in
    let hyp_set = MetadataQuery.signature_of_hypothesis context [] in
    let set = MetadataConstraints.UriManagerSet.union ty_set hyp_set in
      MetadataQuery.close_with_types set [] context 
  in
  (* retrieve equations from the universe universe *)
  (* XXX automation_cache *)
  let universe = automation_cache.AutomationCache.univ in
  let equations = 
    retrieve_equations true signature universe AutoCache.cache_empty context []
  in
  debug_print 
    (lazy ("ho trovato equazioni n. "^(string_of_int (List.length equations))));
  let eqs_and_types =
    HExtlib.filter_map 
      (fun t -> 
         let ty,_ =
           CicTypeChecker.type_of_aux' [] context t CicUniv.oblivion_ugraph
         in
         (* retrieve_equations could also return flexible terms *)
         if is_an_equality ty then Some(t,ty) 
         else
           try
             let ty' = unfold context ty in
             if is_an_equality ty' then Some(t,ty') else None
           with ProofEngineTypes.Fail _ -> None) 
      equations
  in
  let bag = Equality.mk_equality_bag () in

  let bag, units, _, newmeta = 
    partition_unit_equalities context [] (CicMkImplicit.new_meta [] []) bag eqs_and_types 
  in
  let table =
    List.fold_left 
      (fun tbl eq -> Indexing.index tbl eq) 
      Indexing.empty units
  in 
  let changed,(newproof,newmetasenv, newty) =
    Indexing.demod bag
      ([],context,CicUniv.oblivion_ugraph) table initgoal in
  if changed then
    begin
      let oldproof = Equality.Exact bo in
      let proofterm,_ = 
        Equality.build_goal_proof (~contextualize:false) (~forward:true) bag
          eq_uri newproof oldproof ty [] context newmetasenv
      in
      if newmetasenv <> [] then 
	raise (ProofEngineTypes.Fail (lazy ("metasenv not empty")))
      else
	begin
	  assert_proof_is_valid proofterm newmetasenv context newty;
	  match is_subsumed universe context newty with
	    | Some t -> raise 
		(ProofEngineTypes.Fail (lazy ("subsumed by " ^ CicPp.ppterm t)))
	    | None -> close_type proofterm newty context 
	end
    end
  else (* if newty = ty then *)
    raise (ProofEngineTypes.Fail (lazy "no progress"))
  (*else ProofEngineTypes.apply_tactic 
    (ReductionTactics.simpl_tac
      ~pattern:(ProofEngineTypes.conclusion_pattern None)) initialstatus*)
;;      


(* NEW DEMODULATE *)
let demodulate ~dbd ~automation_cache ~params:(univ, params) (proof,goal)= 
  let universe, tables, cache =
     init_cache_and_tables 
       ~dbd ~use_library:false ~use_context:true
       automation_cache univ (proof,goal) 
  in
  let eq_uri = 
    match LibraryObjects.eq_URI () with
      | Some (uri) -> uri
      | None -> raise (ProofEngineTypes.Fail (lazy "equality not declared")) in
  let active, passive, bag = tables in
  let curi,metasenv,subst,pbo,pty, attrs = proof in
  let metano,context,ty = CicUtil.lookup_meta goal metasenv in
  let irl = CicMkImplicit.identity_relocation_list_for_metavariable context in
  let initgoal = [], metasenv, ty in
  let equalities = (Saturation.list_of_passive passive) in
  (* we demodulate using both actives passives *)
  let env = metasenv,context,CicUniv.empty_ugraph in
  debug_print (lazy ("PASSIVES:" ^ string_of_int(List.length equalities)));
  List.iter (fun e -> debug_print (lazy (Equality.string_of_equality ~env e)))
    equalities;
  let table = 
    List.fold_left 
      (fun tbl eq -> Indexing.index tbl eq) 
      (snd active) equalities
  in
  let changed,(newproof,newmetasenv, newty) =
    (* Indexing.demodulation_goal bag *)
      Indexing.demod bag
      (metasenv,context,CicUniv.oblivion_ugraph) table initgoal 
  in
  if changed then
    begin
      let maxm = CicMkImplicit.new_meta metasenv subst in
      let opengoal = Equality.Exact (Cic.Meta(maxm,irl)) in
      let subst_candidates = List.map (fun (i,_,_) -> i) metasenv in
      let subst_candidates = List.filter (fun x-> x <> goal) subst_candidates in
      let proofterm, proto_subst = 
        Equality.build_goal_proof (~contextualize:false) bag
          eq_uri newproof opengoal ty subst_candidates context metasenv
      in
      (* XXX understan what to do with proto subst *)
      let metasenv = (maxm,context,newty)::metasenv in
      let proofterm, _, metasenv, subst, _ =
        CicRefine.type_of metasenv subst context proofterm
          CicUniv.oblivion_ugraph
      in
      let extended_status = (curi,metasenv,subst,pbo,pty, attrs),goal in
      let proof,gl = 
        ProofEngineTypes.apply_tactic 
          (PrimitiveTactics.apply_tac ~term:proofterm) extended_status
      in
        proof,maxm::gl
    end
  else 
    raise (ProofEngineTypes.Fail (lazy "no progress"))
;;

let demodulate_tac ~dbd ~params:(_,flags as params) ~automation_cache =
 ProofEngineTypes.mk_tactic 
  (fun status -> 
    let all = bool flags "all" false in
    if all then
      solve_rewrite ~params ~automation_cache status
    else
      demodulate ~dbd ~params ~automation_cache status)
;;
(***************** applyS *******************)

let apply_smart_aux 
 dbd automation_cache (params:auto_params) proof goal newmeta' metasenv' subst
  context term' ty termty goal_arity 
= 
 let consthead,newmetasenv,arguments,_ =
   TermUtil.saturate_term newmeta' metasenv' context termty goal_arity in
 let term'' = 
   match arguments with 
   | [] -> term' 
   | _ -> Cic.Appl (term'::arguments) 
 in
 let consthead = 
   let rec aux t = function
     | [] -> 
        let t = CicReduction.normalize ~delta:false context t in
        (match t, ty with
        | Cic.Appl (hd1::_), Cic.Appl (hd2::_) when hd1 <> hd2 ->
             let t = ProofEngineReduction.unfold context t in
             (match t with
             | Cic.Appl (hd1'::_) when hd1' = hd2 -> t
             | _ -> raise (ProofEngineTypes.Fail (lazy "incompatible head")))
        | _ -> t)
     | arg :: tl -> 
         match CicReduction.whd context t with
         | Cic.Prod (_,_,tgt) -> 
             aux (CicSubstitution.subst arg tgt) tl
         | _ -> assert false
   in
    aux termty arguments
 in
 let goal_for_paramod =
  match LibraryObjects.eq_URI () with
  | Some uri -> 
      Cic.Appl [Cic.MutInd (uri,0,[]); Cic.Implicit (Some `Type); consthead; ty]
  | None -> raise (ProofEngineTypes.Fail (lazy "No equality defined"))
 in
 try 
   let goal_for_paramod, _, newmetasenv, subst, _ = 
     CicRefine.type_of newmetasenv subst context goal_for_paramod 
       CicUniv.oblivion_ugraph
   in
   let newmeta = CicMkImplicit.new_meta newmetasenv subst in
   let metasenv_for_paramod = (newmeta,context,goal_for_paramod)::newmetasenv in
   let proof'' = 
     let uri,_,_,p,ty, attrs = proof in 
     uri,metasenv_for_paramod,subst,p,ty, attrs 
   in
   let irl = CicMkImplicit.identity_relocation_list_for_metavariable context in
(*
   prerr_endline ("------ prima di rewrite su ------ " ^ string_of_int goal);
   prerr_endline ("menv:\n"^CicMetaSubst.ppmetasenv [] metasenv_for_paramod);
   prerr_endline ("subst:\n"^CicMetaSubst.ppsubst
     ~metasenv:(metasenv_for_paramod)
     subst);
*)

   let (proof''',goals) =
      ProofEngineTypes.apply_tactic 
        (EqualityTactics.rewrite_tac ~direction:`RightToLeft
        ~pattern:(ProofEngineTypes.conclusion_pattern None)
        (Cic.Meta(newmeta,irl)) []) (proof'',goal)
   in
   let goal = match goals with [g] -> g | _ -> assert false in
   let  proof'''', _  =
     ProofEngineTypes.apply_tactic 
       (PrimitiveTactics.apply_tac term'')
       (proof''',goal) 
   in


   let (_,m,_,_,_,_ as p) = 
        let pu,metasenv,subst,proof,px,py = proof'''' in
        let metasenv = CicMetaSubst.apply_subst_metasenv subst metasenv in
        let proof'''' = pu,metasenv,subst,proof,px,py in
        let univ, params = params in
        let use_context = bool params "use_context" true in 
        let universe, (active,passive,bag), cache =
         init_cache_and_tables ~use_library:false ~use_context
           automation_cache univ (proof'''',newmeta)
        in
        match
          Saturation.solve_narrowing bag (proof'''',newmeta) active passive 
            2 (*0 infinity*)
        with 
          | None, active, passive, bag -> 
              raise (ProofEngineTypes.Fail (lazy ("paramod fails")))
          | Some(subst',(pu,metasenv,_,proof,px, py),open_goals),active,
            passive,bag ->
              assert_subst_are_disjoint subst subst';
              let subst = subst@subst' in
              pu,metasenv,subst,proof,px,py
   in

(*
   let (_,m,_,_,_,_ as p),_ = 
      solve_rewrite ~params ~automation_cache (proof'''',newmeta)
   in
*)

   let open_goals = 
     ProofEngineHelpers.compare_metasenvs ~oldmetasenv:metasenv' ~newmetasenv:m
   in
   p, open_goals 
 with
   CicRefine.RefineFailure msg -> 
     raise (ProofEngineTypes.Fail msg)
;;

let apply_smart 
  ~dbd ~term ~automation_cache ~params (proof, goal) 
=
 let module T = CicTypeChecker in
 let module R = CicReduction in
 let module C = Cic in
  let (_,metasenv,subst,_,_, _) = proof in
  let metano,context,ty = CicUtil.lookup_meta goal metasenv in
  let newmeta = CicMkImplicit.new_meta metasenv subst in
   let exp_named_subst_diff,newmeta',newmetasenvfragment,term' =
    match term with
       C.Var (uri,exp_named_subst) ->
        let newmeta',newmetasenvfragment,exp_named_subst',exp_named_subst_diff =
         PrimitiveTactics.generalize_exp_named_subst_with_fresh_metas context newmeta uri
          exp_named_subst
        in
         exp_named_subst_diff,newmeta',newmetasenvfragment,
          C.Var (uri,exp_named_subst')
     | C.Const (uri,exp_named_subst) ->
        let newmeta',newmetasenvfragment,exp_named_subst',exp_named_subst_diff =
         PrimitiveTactics.generalize_exp_named_subst_with_fresh_metas context newmeta uri
          exp_named_subst
        in
         exp_named_subst_diff,newmeta',newmetasenvfragment,
          C.Const (uri,exp_named_subst')
     | C.MutInd (uri,tyno,exp_named_subst) ->
        let newmeta',newmetasenvfragment,exp_named_subst',exp_named_subst_diff =
         PrimitiveTactics.generalize_exp_named_subst_with_fresh_metas context newmeta uri
          exp_named_subst
        in
         exp_named_subst_diff,newmeta',newmetasenvfragment,
          C.MutInd (uri,tyno,exp_named_subst')
     | C.MutConstruct (uri,tyno,consno,exp_named_subst) ->
        let newmeta',newmetasenvfragment,exp_named_subst',exp_named_subst_diff =
         PrimitiveTactics.generalize_exp_named_subst_with_fresh_metas context newmeta uri
          exp_named_subst
        in
         exp_named_subst_diff,newmeta',newmetasenvfragment,
          C.MutConstruct (uri,tyno,consno,exp_named_subst')
     | _ -> [],newmeta,[],term
   in
   let metasenv' = metasenv@newmetasenvfragment in
   let termty,_ = 
     CicTypeChecker.type_of_aux' 
      metasenv' ~subst context term' CicUniv.oblivion_ugraph
   in
   let termty = CicSubstitution.subst_vars exp_named_subst_diff termty in
   let goal_arity = 
     let rec count_prods context ty =
      match CicReduction.whd ~subst context ty with
      | Cic.Prod (n,s,t) -> 1 + count_prods (Some (n,Cic.Decl s)::context) t
      | _ -> 0
     in
       count_prods context ty
   in
    apply_smart_aux dbd automation_cache params proof goal 
     newmeta' metasenv' subst context term' ty termty goal_arity
;;

let applyS_tac ~dbd ~term ~params ~automation_cache =
 ProofEngineTypes.mk_tactic
  (fun status ->
    try 
      apply_smart ~dbd ~term ~params ~automation_cache status
    with 
    | CicUnification.UnificationFailure msg
    | CicTypeChecker.TypeCheckerFailure msg ->
        raise (ProofEngineTypes.Fail msg))
;;


(****************** AUTO ********************)

let calculate_timeout flags = 
    if flags.timeout = 0. then 
      (debug_print (lazy "AUTO WITH NO TIMEOUT");
       {flags with timeout = infinity})
    else 
      flags 
;;
let is_equational_case goalty flags =
  let ensure_equational t = 
    if is_an_equational_goal t then true 
    else false
  in
  (flags.use_paramod && is_an_equational_goal goalty) || 
  (flags.use_only_paramod && ensure_equational goalty)
;;

type menv = Cic.metasenv
type subst = Cic.substitution
type goal = ProofEngineTypes.goal * int * AutoTypes.sort
let candidate_no = ref 0;;
type candidate = int * Cic.term Lazy.t
type cache = AutoCache.cache

type fail = 
  (* the goal (mainly for depth) and key of the goal *)
  goal * AutoCache.cache_key
type op = 
  (* goal has to be proved *)
  | D of goal 
  (* goal has to be cached as a success obtained using candidate as the first
   * step *)
  | S of goal * AutoCache.cache_key * candidate * int 
type elem = 
  (* menv, subst, size, operations done (only S), operations to do, failures to cache if any op fails *)
  menv * subst * int * op list * op list * fail list 
type status = 
  (* list of computations that may lead to the solution: all op list will
   * end with the same (S(g,_)) *)
  elem list
type auto_result = 
  (* menv, subst, alternatives, tables, cache *)
  | Proved of menv * subst * elem list * AutomationCache.tables * cache 
  | Gaveup of AutomationCache.tables * cache 


(* the status exported to the external observer *)  
type auto_status = 
  (* context, (goal,candidate) list, and_list, history *)
  Cic.context * (int * Cic.term * bool * int * (int * Cic.term Lazy.t) list) list * 
  (int * Cic.term * int) list * Cic.term Lazy.t list

let d_prefix l =
  let rec aux acc = function
    | (D g)::tl -> aux (acc@[g]) tl
    | _ -> acc
  in
    aux [] l
;;
let prop_only l =
  List.filter (function (_,_,P) -> true | _ -> false) l
;;

let d_goals l =
  let rec aux acc = function
    | (D g)::tl -> aux (acc@[g]) tl
    | (S _)::tl -> aux acc tl
    | [] -> acc
  in
    aux [] l
;;

let calculate_goal_ty (goalno,_,_) s m = 
  try
    let _,cc,goalty = CicUtil.lookup_meta goalno m in
    (* XXX applicare la subst al contesto? *)
    Some (cc, CicMetaSubst.apply_subst s goalty)
  with CicUtil.Meta_not_found i when i = goalno -> None
;;

let calculate_closed_goal_ty (goalno,_,_) s = 
  try
    let cc,_,goalty = List.assoc goalno s in
    (* XXX applicare la subst al contesto? *)
    Some (cc, CicMetaSubst.apply_subst s goalty)
  with Not_found -> 
    None
;;

let pp_status ctx status = 
  if debug then 
  let names = Utils.names_of_context ctx in
  let pp x = 
    let x = 
      ProofEngineReduction.replace 
        ~equality:(fun a b -> match b with Cic.Meta _ -> true | _ -> false) 
          ~what:[Cic.Rel 1] ~with_what:[Cic.Implicit None] ~where:x
    in
    CicPp.pp x names
  in
  let string_of_do m s (gi,_,_ as g) d =
    match calculate_goal_ty g s m with
    | Some (_,gty) -> Printf.sprintf "D(%d, %s, %d)" gi (pp gty) d
    | None -> Printf.sprintf "D(%d, _, %d)" gi d
  in
  let string_of_s m su k (ci,ct) gi =
    Printf.sprintf "S(%d, %s, %s, %d)" gi (pp k) (pp (Lazy.force ct)) ci
  in
  let string_of_ol m su l =
    String.concat " | " 
      (List.map 
        (function 
          | D (g,d,s) -> string_of_do m su (g,d,s) d 
          | S ((gi,_,_),k,c,_) -> string_of_s m su k c gi) 
        l)
  in
  let string_of_fl m s fl = 
    String.concat " | " 
      (List.map (fun ((i,_,_),ty) -> 
         Printf.sprintf "(%d, %s)" i (pp ty)) fl)
  in
  let rec aux = function
    | [] -> ()
    | (m,s,_,_,ol,fl)::tl ->
        Printf.eprintf "< [%s] ;;; [%s]>\n" 
          (string_of_ol m s ol) (string_of_fl m s fl);
        aux tl
  in
    Printf.eprintf "-------------------------- status -------------------\n";
    aux status;
    Printf.eprintf "-----------------------------------------------------\n";
;;
  
let auto_status = ref [] ;;
let auto_context = ref [];;
let in_pause = ref false;;
let pause b = in_pause := b;;
let cond = Condition.create ();;
let mutex = Mutex.create ();;
let hint = ref None;;
let prune_hint = ref [];;

let step _ = Condition.signal cond;;
let give_hint n = hint := Some n;;
let give_prune_hint hint =
  prune_hint := hint :: !prune_hint
;;

let check_pause _ =
  if !in_pause then
    begin
      Mutex.lock mutex;
      Condition.wait cond mutex;
      Mutex.unlock mutex
    end
;;

let get_auto_status _ = 
  let status = !auto_status in
  let and_list,elems,last = 
    match status with
    | [] -> [],[],[]
    | (m,s,_,don,gl,fail)::tl ->
        let and_list = 
          HExtlib.filter_map 
            (fun (id,d,_ as g) -> 
              match calculate_goal_ty g s m with
              | Some (_,x) -> Some (id,x,d) | None -> None)
            (d_goals gl)
        in
        let rows = 
          (* these are the S goalsin the or list *)
          let orlist = 
            List.map
              (fun (m,s,_,don,gl,fail) -> 
                HExtlib.filter_map
                  (function S (g,k,c,_) -> Some (g,k,c) | _ -> None) 
                  (List.rev don @ gl))
              status
          in
          (* this function eats id from a list l::[id,x] returning x, l *)
          let eat_tail_if_eq id l = 
            let rec aux (s, l) = function
              | [] -> s, l
              | ((id1,_,_),k1,c)::tl when id = id1 ->
                  (match s with
                  | None -> aux (Some c,l) tl
                  | Some _ -> assert false)
              | ((id1,_,_),k1,c as e)::tl -> aux (s, e::l) tl
            in
            let c, l = aux (None, []) l in
            c, List.rev l
          in
          let eat_in_parallel id l =
            let rec aux (b,eaten, new_l as acc) l =
              match l with
              | [] -> acc
              | l::tl ->
                  match eat_tail_if_eq id l with
                  | None, l -> aux (b@[false], eaten, new_l@[l]) tl
                  | Some t,l -> aux (b@[true],eaten@[t], new_l@[l]) tl
            in
            aux ([],[],[]) l
          in
          let rec eat_all rows l =
            match l with
            | [] -> rows
            | elem::or_list ->
                match List.rev elem with
                | ((to_eat,depth,_),k,_)::next_lunch ->
                    let b, eaten, l = eat_in_parallel to_eat l in
                    let eaten = HExtlib.list_uniq eaten in
                    let eaten = List.rev eaten in
                    let b = true (* List.hd (List.rev b) *) in
                    let rows = rows @ [to_eat,k,b,depth,eaten] in
                    eat_all rows l
                | [] -> eat_all rows or_list
          in
          eat_all [] (List.rev orlist)
        in
        let history = 
          HExtlib.filter_map
            (function (S (_,_,(_,c),_)) -> Some c | _ -> None) 
            gl 
        in
(*         let rows = List.filter (fun (_,l) -> l <> []) rows in *)
        and_list, rows, history
  in
  !auto_context, elems, and_list, last
;;

(* Works if there is no dependency over proofs *)
let is_a_green_cut goalty =
  CicUtil.is_meta_closed goalty
;;
let rec first_s = function
  | (D _)::tl -> first_s tl
  | (S (g,k,c,s))::tl -> Some ((g,k,c,s),tl)
  | [] -> None
;;
let list_union l1 l2 =
  (* TODO ottimizzare compare *)
  HExtlib.list_uniq (List.sort compare (l1 @ l1))
;;
let rec eq_todo l1 l2 =
  match l1,l2 with
  | (D g1) :: tl1,(D g2) :: tl2 when g1=g2 -> eq_todo tl1 tl2
  | (S (g1,k1,(c1,lt1),i1)) :: tl1, (S (g2,k2,(c2,lt2),i2)) :: tl2
    when i1 = i2 && g1 = g2 && k1 = k2 && c1 = c2 ->
      if Lazy.force lt1 = Lazy.force lt2 then eq_todo tl1 tl2 else false
  | [],[] -> true
  | _ -> false
;;
let eat_head todo id fl orlist = 
  let rec aux acc = function
  | [] -> [], acc
  | (m, s, _, _, todo1, fl1)::tl as orlist -> 
      let rec aux1 todo1 =
        match first_s todo1 with
        | None -> orlist, acc
        | Some (((gno,_,_),_,_,_), todo11) ->
            (* TODO confronto tra todo da ottimizzare *)
            if gno = id && eq_todo todo11 todo then 
              aux (list_union fl1 acc) tl
            else 
              aux1 todo11
      in
       aux1 todo1
  in 
    aux fl orlist
;;
let close_proof p ty menv context = 
  let metas =
    List.map fst (CicUtil.metas_of_term p @ CicUtil.metas_of_term ty)
  in
  let menv = List.filter (fun (i,_,_) -> List.exists ((=)i) metas) menv in
  naif_closure p menv context
;;
(* XXX capire bene quando aggiungere alla cache *)
let add_to_cache_and_del_from_orlist_if_green_cut
  g s m cache key todo orlist fl ctx size minsize
= 
  let cache = cache_remove_underinspection cache key in
  (* prima per fare la irl usavamo il contesto vero e proprio e non quello 
   * canonico! XXX *)
  match calculate_closed_goal_ty g s with
  | None -> assert false
  | Some (canonical_ctx , gty) ->
      let goalno,depth,sort = g in
      let irl = mk_irl canonical_ctx in
      let goal = Cic.Meta(goalno, irl) in
      let proof = CicMetaSubst.apply_subst s goal in
      let green_proof, closed_proof = 
        let b = is_a_green_cut proof in
        if not b then
          b, (* close_proof proof gty m ctx *) proof 
        else
          b, proof
      in
      debug_print (lazy ("TENTATIVE CACHE: " ^ CicPp.ppterm key));
      if is_a_green_cut key then
        (* if the initia goal was closed, we cut alternatives *)
        let _ = debug_print (lazy ("MANGIO: " ^ string_of_int goalno)) in
        let orlist, fl = eat_head todo goalno fl orlist in
        let cache = 
          if size < minsize then 
            (debug_print (lazy ("NO CACHE: 2 (size <= minsize)"));cache)
          else 
          (* if the proof is closed we cache it *)
          if green_proof then cache_add_success cache key proof
          else (* cache_add_success cache key closed_proof *) 
            (debug_print (lazy ("NO CACHE: (no gree proof)"));cache)
        in
        cache, orlist, fl, true
      else
        let cache = 
          debug_print (lazy ("TENTATIVE CACHE: " ^ CicPp.ppterm gty));
          if size < minsize then 
            (debug_print (lazy ("NO CACHE: (size <= minsize)")); cache) else
          (* if the substituted goal and the proof are closed we cache it *)
          if is_a_green_cut gty then
            if green_proof then cache_add_success cache gty proof
            else (* cache_add_success cache gty closed_proof *) 
              (debug_print (lazy ("NO CACHE: (no green proof (gty))"));cache)
          else (*
            try
              let ty, _ =
                CicTypeChecker.type_of_aux' ~subst:s 
                  m ctx closed_proof CicUniv.oblivion_ugraph
              in
              if is_a_green_cut ty then 
                cache_add_success cache ty closed_proof
              else cache
            with
            | CicTypeChecker.TypeCheckerFailure _ ->*) 
          (debug_print (lazy ("NO CACHE: (no green gty )"));cache)
        in
        cache, orlist, fl, false
;;
let close_failures (fl : fail list) (cache : cache) = 
  List.fold_left 
    (fun cache ((gno,depth,_),gty) -> 
      if CicUtil.is_meta_closed gty then
       ( debug_print (lazy ("FAIL: INDUCED: " ^ string_of_int gno));
         cache_add_failure cache gty depth) 
      else
         cache)
    cache fl
;;
let put_in_subst subst metasenv  (goalno,_,_) canonical_ctx t ty =
  let entry = goalno, (canonical_ctx, t,ty) in
  assert_subst_are_disjoint subst [entry];
  let subst = entry :: subst in
  
  let metasenv = CicMetaSubst.apply_subst_metasenv subst metasenv in

  subst, metasenv
;;

let mk_fake_proof metasenv subst (goalno,_,_) goalty context = 
  None,metasenv,subst ,(lazy (Cic.Meta(goalno,mk_irl context))),goalty, [] 
;;

let equational_case 
  tables cache depth fake_proof goalno goalty subst context 
    flags
=
  let active,passive,bag = tables in
  let ppterm = ppterm context in
  let status = (fake_proof,goalno) in
    if flags.use_only_paramod then
      begin
        debug_print (lazy ("PARAMODULATION SU: " ^ 
                         string_of_int goalno ^ " " ^ ppterm goalty ));
        let goal_steps, saturation_steps, timeout =
          max_int,max_int,flags.timeout 
        in
        match
          Saturation.given_clause bag status active passive 
            goal_steps saturation_steps timeout
        with 
          | None, active, passive, bag -> 
              [], (active,passive,bag), cache, flags
          | Some(subst',(_,metasenv,_subst,proof,_, _),open_goals),active,
            passive,bag ->
              assert_subst_are_disjoint subst subst';
              let subst = subst@subst' in
              let open_goals = 
                order_new_goals metasenv subst open_goals ppterm 
              in
              let open_goals = 
                List.map (fun (x,sort) -> x,depth-1,sort) open_goals 
              in
              incr candidate_no;
              [(!candidate_no,proof),metasenv,subst,open_goals], 
                (active,passive,bag), cache, flags
      end
    else
      begin
        debug_print (lazy ("NARROWING DEL GOAL: " ^ 
                         string_of_int goalno ^ " " ^ ppterm goalty ));
        let goal_steps, saturation_steps, timeout =
          1,0,flags.timeout 
        in
        match
          Saturation.solve_narrowing bag status active passive goal_steps 
        with 
          | None, active, passive, bag -> 
              [], (active,passive,bag), cache, flags
          | Some(subst',(_,metasenv,_subst,proof,_, _),open_goals),active,
            passive,bag ->
              assert_subst_are_disjoint subst subst';
              let subst = subst@subst' in
              let open_goals = 
                order_new_goals metasenv subst open_goals ppterm 
              in
              let open_goals = 
                List.map (fun (x,sort) -> x,depth-1,sort) open_goals 
              in
              incr candidate_no;
              [(!candidate_no,proof),metasenv,subst,open_goals], 
                (active,passive,bag), cache, flags
      end
(*
      begin
        let params = ([],["use_context","false"]) in
        let automation_cache = { 
              AutomationCache.tables = tables ;
              AutomationCache.univ = Universe.empty; }
        in
        try 
          let ((_,metasenv,subst,_,_,_),open_goals) =

            solve_rewrite ~params ~automation_cache
              (fake_proof, goalno)
          in
          let proof = lazy (Cic.Meta (-1,[])) in
          [(!candidate_no,proof),metasenv,subst,[]],tables, cache, flags
        with ProofEngineTypes.Fail _ -> [], tables, cache, flags
(*
        let res = Saturation.all_subsumed bag status active passive in
        let res' =
          List.map 
            (fun (subst',(_,metasenv,_subst,proof,_, _),open_goals) ->
               assert_subst_are_disjoint subst subst';
               let subst = subst@subst' in
               let open_goals = 
                 order_new_goals metasenv subst open_goals ppterm 
               in
               let open_goals = 
                 List.map (fun (x,sort) -> x,depth-1,sort) open_goals 
               in
               incr candidate_no;
                 (!candidate_no,proof),metasenv,subst,open_goals)
            res 
          in
          res', (active,passive,bag), cache, flags 
*)
      end
*)
;;

let sort_new_elems = 
 List.sort (fun (_,_,_,l1) (_,_,_,l2) -> 
         let p1 = List.length (prop_only l1) in 
         let p2 = List.length (prop_only l2) in
         if p1 = p2 then List.length l1 - List.length l2 else p1-p2)
;;


let try_candidate dbd
  goalty tables subst fake_proof goalno depth context cand 
=
  let ppterm = ppterm context in
  try 
    let actives, passives, bag = tables in 
    let (_,metasenv,subst,_,_,_), open_goals =
       ProofEngineTypes.apply_tactic
        (PrimitiveTactics.apply_tac ~term:cand)
        (fake_proof,goalno) 
    in
    let tables = actives, passives, 
      Equality.push_maxmeta bag 
        (max (Equality.maxmeta bag) (CicMkImplicit.new_meta metasenv subst)) 
    in
    debug_print (lazy ("   OK: " ^ ppterm cand));
    let metasenv = CicRefine.pack_coercion_metasenv metasenv in
    let open_goals = order_new_goals metasenv subst open_goals ppterm in
    let open_goals = List.map (fun (x,sort) -> x,depth-1,sort) open_goals in
    incr candidate_no;
    Some ((!candidate_no,lazy cand),metasenv,subst,open_goals), tables 
  with 
    | ProofEngineTypes.Fail s -> None,tables
    | CicUnification.Uncertain s ->  None,tables
;;

let applicative_case dbd
  tables depth subst fake_proof goalno goalty metasenv context 
  signature universe cache flags
= 
  (* let goalty_aux = 
    match goalty with
    | Cic.Appl (hd::tl) -> 
        Cic.Appl (hd :: HExtlib.mk_list (Cic.Meta (0,[])) (List.length tl))
    | _ -> goalty
  in *)
  let goalty_aux = goalty in
  let candidates = 
    get_candidates flags.skip_trie_filtering universe cache goalty_aux
  in
  (* if the goal is an equality we skip the congruence theorems 
  let candidates =
    if is_equational_case goalty flags 
    then List.filter not_default_eq_term candidates 
    else candidates 
  in *)
  let candidates = List.filter (only signature context metasenv) candidates 
  in
  let tables, elems = 
    List.fold_left 
      (fun (tables,elems) cand ->
        match 
          try_candidate dbd goalty
            tables subst fake_proof goalno depth context cand
        with
        | None, tables -> tables, elems
        | Some x, tables -> tables, x::elems)
      (tables,[]) candidates
  in
  let elems = sort_new_elems elems in
  elems, tables, cache
;;

let try_smart_candidate dbd
  goalty tables subst fake_proof goalno depth context cand 
=
  let ppterm = ppterm context in
  try
    let params = (None,[]) in
    let automation_cache = { 
          AutomationCache.tables = tables ;
          AutomationCache.univ = Universe.empty; }
    in
    debug_print (lazy ("candidato per " ^ string_of_int goalno 
      ^ ": " ^ CicPp.ppterm cand));
(*
    let (_,metasenv,subst,_,_,_) = fake_proof in
    prerr_endline ("metasenv:\n" ^ CicMetaSubst.ppmetasenv [] metasenv);
    prerr_endline ("subst:\n" ^ CicMetaSubst.ppsubst ~metasenv subst);
*)
    let ((_,metasenv,subst,_,_,_),open_goals) =
      apply_smart ~dbd ~term:cand ~params ~automation_cache
        (fake_proof, goalno)
    in
    let metasenv = CicRefine.pack_coercion_metasenv metasenv in
    let open_goals = order_new_goals metasenv subst open_goals ppterm in
    let open_goals = List.map (fun (x,sort) -> x,depth-1,sort) open_goals in
    incr candidate_no;
    Some ((!candidate_no,lazy cand),metasenv,subst,open_goals), tables 
  with 
  | ProofEngineTypes.Fail s -> None,tables
  | CicUnification.Uncertain s ->  None,tables
;;

let smart_applicative_case dbd
  tables depth subst fake_proof goalno goalty metasenv context signature
  universe cache flags
= 
  let goalty_aux = 
    match goalty with
    | Cic.Appl (hd::tl) -> 
        Cic.Appl (hd :: HExtlib.mk_list (Cic.Meta (0,[])) (List.length tl))
    | _ -> goalty
  in
  let smart_candidates = 
    get_candidates flags.skip_trie_filtering universe cache goalty_aux
  in
  let candidates = 
    get_candidates flags.skip_trie_filtering universe cache goalty
  in
  let smart_candidates = 
    List.filter
      (fun x -> not(List.mem x candidates)) smart_candidates
  in 
  let debug_msg =
    (lazy ("smart_candidates" ^ " = " ^ 
             (String.concat "\n" (List.map CicPp.ppterm smart_candidates)))) in
  debug_print debug_msg;
  let candidates = List.filter (only signature context metasenv) candidates in
  let smart_candidates = 
    List.filter (only signature context metasenv) smart_candidates 
  in
(*
  let penalty cand depth = 
    if only signature context metasenv cand then depth else ((prerr_endline (
    "penalizzo " ^ CicPp.ppterm cand));depth -1)
  in
*)
  let tables, elems = 
    List.fold_left 
      (fun (tables,elems) cand ->
        match 
          try_candidate dbd goalty
            tables subst fake_proof goalno depth context cand
        with
        | None, tables ->
            (* if normal application fails we try to be smart *)
	    (match try_smart_candidate dbd goalty
               tables subst fake_proof goalno depth context cand
	     with
	       | None, tables -> tables, elems
               | Some x, tables -> tables, x::elems)
        | Some x, tables -> tables, x::elems)
      (tables,[]) candidates
  in
  let tables, smart_elems = 
      List.fold_left 
        (fun (tables,elems) cand ->
          match 
            try_smart_candidate dbd goalty
              tables subst fake_proof goalno depth context cand
          with
          | None, tables -> tables, elems
          | Some x, tables -> tables, x::elems)
        (tables,[]) smart_candidates
  in
  let elems = sort_new_elems (elems @ smart_elems) in
  elems, tables, cache
;;

let equational_and_applicative_case dbd
  signature universe flags m s g gty tables cache context 
=
  let goalno, depth, sort = g in
  let fake_proof = mk_fake_proof m s g gty context in
  if is_equational_case gty flags then
    let elems,tables,cache, flags =
      equational_case tables cache
        depth fake_proof goalno gty s context flags 
    in
    let more_elems, tables, cache =
      if flags.use_only_paramod then
        [],tables, cache
      else
        applicative_case dbd
          tables depth s fake_proof goalno 
            gty m context signature universe cache flags
    in
      elems@more_elems, tables, cache, flags            
  else
    let elems, tables, cache =
      match LibraryObjects.eq_URI () with
      | Some _ ->
         smart_applicative_case dbd tables depth s fake_proof goalno 
           gty m context signature universe cache flags
      | None -> 
         applicative_case dbd tables depth s fake_proof goalno 
           gty m context signature universe cache flags
    in
      elems, tables, cache, flags  
;;
let rec condition_for_hint i = function
  | [] -> false
  | S (_,_,(j,_),_):: tl -> j <> i (* && condition_for_hint i tl *)
  | _::tl -> condition_for_hint i tl
;;
let remove_s_from_fl (id,_,_) (fl : fail list) =
  let rec aux = function
    | [] -> []
    | ((id1,_,_),_)::tl when id = id1 -> tl
    | hd::tl ->  hd :: aux tl
  in 
    aux fl
;;

let prunable_for_size flags s m todo =
  let rec aux b = function
    | (S _)::tl -> aux b tl
    | (D (_,_,T))::tl -> aux b tl
    | (D g)::tl -> 
	(match calculate_goal_ty g s m with
          | None -> aux b tl
	  | Some (canonical_ctx, gty) -> 
            let gsize, _ = 
              Utils.weight_of_term 
		~consider_metas:false ~count_metas_occurrences:true gty in
	    let newb = b || gsize > flags.maxgoalsizefactor in
	    aux newb tl)
    | [] -> b
  in
    aux false todo

(*
let prunable ty todo =
  let rec aux b = function
    | (S(_,k,_,_))::tl -> aux (b || Equality.meta_convertibility k ty) tl
    | (D (_,_,T))::tl -> aux b tl
    | D _::_ -> false
    | [] -> b
  in
    aux false todo
;;
*)

let prunable menv subst ty todo =
  let rec aux = function
    | (S(_,k,_,_))::tl ->
	 (match Equality.meta_convertibility_subst k ty menv with
	  | None -> aux tl
	  | Some variant -> 
	       no_progress variant tl (* || aux tl*))
    | (D (_,_,T))::tl -> aux tl
    | _ -> false
  and no_progress variant = function
    | [] -> (*prerr_endline "++++++++++++++++++++++++ no_progress";*) true
    | D ((n,_,P) as g)::tl -> 
	(match calculate_goal_ty g subst menv with
           | None -> no_progress variant tl
           | Some (_, gty) -> 
	       (match calculate_goal_ty g variant menv with
		  | None -> assert false
		  | Some (_, gty') ->
		      if gty = gty' then no_progress variant tl
(* 
(prerr_endline (string_of_int n);
 prerr_endline (CicPp.ppterm gty);
 prerr_endline (CicPp.ppterm gty');
 prerr_endline "---------- subst";
 prerr_endline (CicMetaSubst.ppsubst ~metasenv:menv subst);
 prerr_endline "---------- variant";
 prerr_endline (CicMetaSubst.ppsubst ~metasenv:menv variant);
 prerr_endline "---------- menv";
 prerr_endline (CicMetaSubst.ppmetasenv [] menv); 
			 no_progress variant tl) *)
		      else false))
    | _::tl -> no_progress variant tl
  in
    aux todo

;;
let condition_for_prune_hint prune (m, s, size, don, todo, fl) =
  let s = 
    HExtlib.filter_map (function S (_,_,(c,_),_) -> Some c | _ -> None) todo 
  in
  List.for_all (fun i -> List.for_all (fun j -> i<>j) prune) s
;;
let filter_prune_hint c l =
  let prune = !prune_hint in
  prune_hint := []; (* possible race... *)
  if prune = [] then c,l
  else 
    cache_reset_underinspection c,      
    List.filter (condition_for_prune_hint prune) l
;;

let auto_main dbd tables context flags signature universe cache elems =
  auto_context := context;
  let rec aux tables flags cache (elems : status) =
    pp_status context elems;
(* DEBUGGING CODE: uncomment these two lines to stop execution at each iteration
    auto_status := elems;
    check_pause ();
*)
    let cache, elems = filter_prune_hint cache elems in
    match elems with
    | (m, s, size, don, todo, fl)::orlist when !hint <> None ->
	debug_print (lazy "skip");
        (match !hint with
        | Some i when condition_for_hint i todo ->
            aux tables flags cache orlist
        | _ ->
          hint := None;
          aux tables flags cache elems)
    | [] ->
        (* complete failure *)
        debug_print (lazy "give up");
        Gaveup (tables, cache)
    | (m, s, _, _, [],_)::orlist ->
        (* complete success *)
        debug_print (lazy "success");
        Proved (m, s, orlist, tables, cache)
    | (m, s, size, don, (D (_,_,T))::todo, fl)::orlist 
      when not flags.AutoTypes.do_types ->
        (* skip since not Prop, don't even check if closed by side-effect *)
        debug_print (lazy "skip existential goal");
        aux tables flags cache ((m, s, size, don, todo, fl)::orlist)
    | (m, s, size, don, (S(g, key, c,minsize) as op)::todo, fl)::orlist ->
        (* partial success, cache g and go on *)
        let cache, orlist, fl, sibling_pruned = 
          add_to_cache_and_del_from_orlist_if_green_cut 
            g s m cache key todo orlist fl context size minsize
        in
        debug_print (lazy (AutoCache.cache_print context cache));
        let fl = remove_s_from_fl g fl in
        let don = if sibling_pruned then don else op::don in
        aux tables flags cache ((m, s, size, don, todo, fl)::orlist)
    | (m, s, size, don, todo, fl)::orlist 
      when List.length(prop_only (d_goals todo)) > flags.maxwidth ->
        debug_print (lazy ("FAIL: WIDTH"));
        (* too many goals in and generated by last th *)
        let cache = close_failures fl cache in
        aux tables flags cache orlist
    | (m, s, size, don, todo, fl)::orlist when size > flags.maxsize ->
        debug_print 
          (lazy ("FAIL: SIZE: "^string_of_int size ^ 
            " > " ^ string_of_int flags.maxsize ));
        (* we already have a too large proof term *)
        let cache = close_failures fl cache in
        aux tables flags cache orlist
    | _ when Unix.gettimeofday () > flags.timeout ->
        (* timeout *)
        debug_print (lazy ("FAIL: TIMEOUT"));
        Gaveup (tables, cache)
    | (m, s, size, don, (D (gno,depth,_ as g))::todo, fl)::orlist as status ->
        (* attack g *) 
        debug_print (lazy "attack goal");
        match calculate_goal_ty g s m with
        | None -> 
            (* closed by side effect *)
            debug_print (lazy ("SUCCESS: SIDE EFFECT: " ^ string_of_int gno));
            aux tables flags cache ((m,s,size,don,todo, fl)::orlist)
        | Some (canonical_ctx, gty) ->
            let gsize, _ = 
              Utils.weight_of_term ~consider_metas:false ~count_metas_occurrences:true gty 
            in
            if gsize > flags.maxgoalsizefactor then
	      (debug_print (lazy ("FAIL: SIZE: goal: "^string_of_int gsize));
               aux tables flags cache orlist)
            else if prunable_for_size flags s m todo then
		(debug_print (lazy ("POTO at depth: "^(string_of_int depth)));
	         aux tables flags cache orlist)
	    else
            (* still to be proved *)
            (debug_print (lazy ("EXAMINE: "^CicPp.ppterm gty));
            match cache_examine cache gty with
            | Failed_in d when d >= depth -> 
                (* fail depth *)
                debug_print (lazy ("FAIL: DEPTH (cache): "^string_of_int gno));
                let cache = close_failures fl cache in
                aux tables flags cache orlist
            | UnderInspection -> 
                (* fail loop *)
                debug_print (lazy ("FAIL: LOOP: " ^ string_of_int gno));
                let cache = close_failures fl cache in
                aux tables flags cache orlist
            | Succeded t -> 
                debug_print (lazy ("SUCCESS: CACHE HIT: " ^ string_of_int gno));
                let s, m = put_in_subst s m g canonical_ctx t gty in
                aux tables flags cache ((m, s, size, don,todo, fl)::orlist)
            | Notfound 
            | Failed_in _ when depth > 0 -> 
                ( (* more depth or is the first time we see the goal *)
                    if prunable m s gty todo then
                      (debug_print (lazy(
                         "FAIL: LOOP: one father is equal"));
                       aux tables flags cache orlist)
                    else
                    let cache = cache_add_underinspection cache gty depth in
                    auto_status := status;
                    check_pause ();
                    debug_print 
                      (lazy ("INSPECTING: " ^ 
                        string_of_int gno ^ "("^ string_of_int size ^ "): "^
                        CicPp.ppterm gty));
                    (* elems are possible computations for proving gty *)
                    let elems, tables, cache, flags =
                      equational_and_applicative_case dbd
                        signature universe flags m s g gty tables cache context
                    in
                    if elems = [] then
                      (* this goal has failed *)
                      let cache = close_failures ((g,gty)::fl) cache in
                      aux tables flags cache orlist
                    else
                      (* elems = (cand,m,s,gl) *)
                      let size_gl l = List.length 
                        (List.filter (function (_,_,P) -> true | _ -> false) l) 
                      in
                      let elems = 
                        let inj_gl gl = List.map (fun g -> D g) gl in
                        let rec map = function
                          | [] -> assert false
                          | (cand,m,s,gl)::[] ->
                              (* in the last one we add the failure *)
                              let todo = 
                                inj_gl gl @ (S(g,gty,cand,size+1))::todo 
                              in
                              (* we are the last in OR, we fail on g and 
                               * also on all failures implied by g *)
                              (m,s, size + size_gl gl, don, todo, (g,gty)::fl)
                              :: orlist
                          | (cand,m,s,gl)::tl -> 
                              (* we add the S step after gl and before todo *)
                              let todo = 
                                inj_gl gl @ (S(g,gty,cand,size+1))::todo 
                              in
                              (* since we are not the last in OR, we do not
                               * imply failures *)
                              (m,s, size + size_gl gl, don, todo, []) :: map tl
                        in
                          map elems
                      in
                        aux tables flags cache elems)
            | _ -> 
                (* no more depth *)
                debug_print (lazy ("FAIL: DEPTH: " ^ string_of_int gno));
                let cache = close_failures fl cache in
                aux tables flags cache orlist)
  in
    (aux tables flags cache elems : auto_result)
;;
    

let
  auto_all_solutions dbd tables universe cache context metasenv gl flags 
=
  let signature =
    List.fold_left 
      (fun set g ->
	 MetadataConstraints.UriManagerSet.union set 
	     (MetadataQuery.signature_of metasenv g)
       )
      MetadataConstraints.UriManagerSet.empty gl 
  in
  let goals = order_new_goals metasenv [] gl CicPp.ppterm in
  let goals = 
    List.map 
      (fun (x,s) -> D (x,flags.maxdepth,s)) goals 
  in
  let elems = [metasenv,[],1,[],goals,[]] in
  let rec aux tables solutions cache elems flags =
    match auto_main dbd tables context flags signature universe cache elems with
    | Gaveup (tables,cache) ->
        solutions,cache, tables
    | Proved (metasenv,subst,others,tables,cache) -> 
        if Unix.gettimeofday () > flags.timeout then
          ((subst,metasenv)::solutions), cache, tables
        else
          aux tables ((subst,metasenv)::solutions) cache others flags
  in
  let rc = aux tables [] cache elems flags in
    match rc with
    | [],cache,tables -> [],cache,tables
    | solutions, cache,tables -> 
        let solutions = 
          HExtlib.filter_map
            (fun (subst,newmetasenv) ->
              let opened = 
                ProofEngineHelpers.compare_metasenvs ~oldmetasenv:metasenv ~newmetasenv
              in
              if opened = [] then Some subst else None)
            solutions
        in
         solutions,cache,tables
;;

(******************* AUTO ***************)


let auto dbd flags metasenv tables universe cache context metasenv gl =
  let initial_time = Unix.gettimeofday() in  
  let signature =
    List.fold_left 
      (fun set g ->
	 MetadataConstraints.UriManagerSet.union set 
	     (MetadataQuery.signature_of metasenv g)
       )
      MetadataConstraints.UriManagerSet.empty gl 
  in
  let goals = order_new_goals metasenv [] gl CicPp.ppterm in
  let goals = List.map (fun (x,s) -> D(x,flags.maxdepth,s)) goals in
  let elems = [metasenv,[],1,[],goals,[]] in
  match auto_main dbd tables context flags signature universe cache elems with
  | Proved (metasenv,subst,_, tables,cache) -> 
      debug_print(lazy
        ("TIME:"^string_of_float(Unix.gettimeofday()-.initial_time)));
      Some (subst,metasenv), cache
  | Gaveup (tables,cache) -> 
      debug_print(lazy
        ("TIME:"^string_of_float(Unix.gettimeofday()-.initial_time)));
      None,cache
;;

let auto_tac ~(dbd:HSql.dbd) ~params:(univ,params) ~automation_cache (proof, goal) =
  let flags = flags_of_params params () in
  let use_library = flags.use_library in
  let universe, tables, cache =
    init_cache_and_tables 
     ~dbd ~use_library ~use_context:(not flags.skip_context)
     automation_cache univ (proof, goal) 
  in
  let _,metasenv,subst,_,_, _ = proof in
  let _,context,goalty = CicUtil.lookup_meta goal metasenv in
  let signature = MetadataQuery.signature_of metasenv goal in
  let signature =
    match univ with
      | None -> signature
      | Some l -> 
	  List.fold_left 
	    (fun set t ->
               let ty, _ = 
		 CicTypeChecker.type_of_aux' metasenv context t 
		   CicUniv.oblivion_ugraph
	       in
		 MetadataConstraints.UriManagerSet.union set 
		   (MetadataConstraints.constants_of ty)
	    )
	    signature l
  in
  let tables,cache =
    if flags.close_more then
      close_more 
        tables context (proof, goal) 
          (auto_all_solutions dbd) signature universe cache 
    else tables,cache in
  let initial_time = Unix.gettimeofday() in
  let (_,oldmetasenv,_,_,_, _) = proof in
    hint := None;
  let elem = 
    metasenv,subst,1,[],[D (goal,flags.maxdepth,P)],[]
  in
  match auto_main dbd tables context flags signature universe cache [elem] with
    | Proved (metasenv,subst,_, tables,cache) -> 
        debug_print (lazy 
          ("TIME:"^string_of_float(Unix.gettimeofday()-.initial_time)));
        let proof,metasenv =
        ProofEngineHelpers.subst_meta_and_metasenv_in_proof
          proof goal subst metasenv
        in
        let opened = 
          ProofEngineHelpers.compare_metasenvs ~oldmetasenv
            ~newmetasenv:metasenv
        in
          proof,opened
    | Gaveup (tables,cache) -> 
        debug_print
          (lazy ("TIME:"^
            string_of_float(Unix.gettimeofday()-.initial_time)));
        raise (ProofEngineTypes.Fail (lazy "Auto gave up"))
;;

let auto_tac ~dbd ~params ~automation_cache = 
  ProofEngineTypes.mk_tactic (auto_tac ~params ~dbd ~automation_cache);;

let pp_proofterm = Equality.pp_proofterm;;

let revision = "$Revision$";;
let size_and_depth context metasenv t = 100, 100

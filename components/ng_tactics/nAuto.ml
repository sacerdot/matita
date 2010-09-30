(*
    ||M||  This file is part of HELM, an Hypertextual, Electronic        
    ||A||  Library of Mathematics, developed at the Computer Science     
    ||T||  Department, University of Bologna, Italy.                     
    ||I||                                                                
    ||T||  HELM is free software; you can redistribute it and/or         
    ||A||  modify it under the terms of the GNU General Public License   
    \   /  version 2 or (at your option) any later version.      
     \ /   This software is distributed as is, NO WARRANTY.     
      V_______________________________________________________________ *)

(* $Id: nCic.ml 9058 2008-10-13 17:42:30Z tassi $ *)

open Printf

let debug = ref true
let debug_print ?(depth=0) s = 
  if !debug then prerr_endline (String.make depth '\t'^Lazy.force s) else ()
let debug_do f = if !debug then f () else ()

open Continuationals.Stack
open NTacStatus
module Ast = CicNotationPt

(* =================================== paramod =========================== *)
let auto_paramod ~params:(l,_) status goal =
  let l = match l with
    | None -> raise (Error (lazy "no proof found",None))
    | Some l -> l in
  let gty = get_goalty status goal in
  let n,h,metasenv,subst,o = status#obj in
  let status,t = term_of_cic_term status gty (ctx_of gty) in
  let status, l = 
    List.fold_left
      (fun (status, l) t ->
        let status, t = disambiguate status (ctx_of gty) t None in
        let status, ty = typeof status (ctx_of t) t in
        let status, t =  term_of_cic_term status t (ctx_of gty) in
        let status, ty = term_of_cic_term status ty (ctx_of ty) in
        (status, (t,ty) :: l))
      (status,[]) l
  in
  match
    NCicParamod.nparamod status metasenv subst (ctx_of gty) (NCic.Rel ~-1,t) l 
  with
  | [] -> raise (Error (lazy "no proof found",None))
  | (pt, _, metasenv, subst)::_ -> 
      let status = status#set_obj (n,h,metasenv,subst,o) in
      instantiate status goal (mk_cic_term (ctx_of gty) pt)
;;

let auto_paramod_tac ~params status = 
  NTactics.distribute_tac (auto_paramod ~params) status
;;

(* =================================== auto =========================== *)
(****************** AUTO ********************

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
    let params = ([],[]) in
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
    List.fold_left 
      (fun set t ->
         let ty, _ = 
	   CicTypeChecker.type_of_aux' metasenv context t 
	     CicUniv.oblivion_ugraph
	 in
	 MetadataConstraints.UriManagerSet.union set 
	   (MetadataConstraints.constants_of ty)
       )
      signature univ
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
*)


type th_cache = (NCic.context * InvRelDiscriminationTree.t) list

let keys_of_term status t =
  let status, orig_ty = typeof status (ctx_of t) t in
  let _, ty, _ = saturate ~delta:max_int status orig_ty in
  let keys = [ty] in
  let keys = 
    let _, ty = term_of_cic_term status ty (ctx_of ty) in
    match ty with
    | NCic.Const (NReference.Ref (_,NReference.Def h)) 
    | NCic.Appl (NCic.Const(NReference.Ref(_,NReference.Def h))::_) 
       when h > 0 ->
         let _,ty,_= saturate status ~delta:(h-1) orig_ty in
         ty::keys
    | _ -> keys
  in
  status, keys
;;

let mk_th_cache status gl = 
  List.fold_left 
    (fun (status, acc) g ->
       let gty = get_goalty status g in
       let ctx = ctx_of gty in
       debug_print(lazy("th cache for: "^ppterm status gty));
       debug_print(lazy("th cache in: "^ppcontext status ctx));
       if List.mem_assq ctx acc then status, acc else
         let idx = InvRelDiscriminationTree.empty in
         let status,_,idx = 
           List.fold_left 
             (fun (status, i, idx) _ -> 
                let t = mk_cic_term ctx (NCic.Rel i) in
                debug_print(lazy("indexing: "^ppterm status t));
                let status, keys = keys_of_term status t in
                let idx =
                  List.fold_left (fun idx k -> 
                    InvRelDiscriminationTree.index idx k t) idx keys
                in
                status, i+1, idx)
             (status, 1, idx) ctx
          in
         status, (ctx, idx) :: acc)
    (status,[]) gl
;;

let add_to_th t c ty = 
  let key_c = ctx_of t in
  if not (List.mem_assq key_c c) then
      (key_c ,InvRelDiscriminationTree.index 
               InvRelDiscriminationTree.empty ty t ) :: c 
  else
    let rec replace = function
      | [] -> []
      | (x, idx) :: tl when x == key_c -> 
          (x, InvRelDiscriminationTree.index idx ty t) :: tl
      | x :: tl -> x :: replace tl
    in 
      replace c
;;

let pp_idx status idx =
   InvRelDiscriminationTree.iter idx
      (fun k set ->
         debug_print(lazy("K: " ^ NCicInverseRelIndexable.string_of_path k));
         Ncic_termSet.iter 
           (fun t -> debug_print(lazy("\t"^ppterm status t))) 
           set)
;;

let pp_th status = 
  List.iter 
    (fun ctx, idx ->
       debug_print(lazy( "-----------------------------------------------"));
       debug_print(lazy( (NCicPp.ppcontext ~metasenv:[] ~subst:[] ctx)));
       debug_print(lazy( "||====>  "));
       pp_idx status idx)
;;


let search_in_th gty th = 
  let c = ctx_of gty in
  let rec aux acc = function
   | [] -> Ncic_termSet.elements acc
   | (_::tl) as k ->
       try 
         let idx = List.assq k th in
         let acc = Ncic_termSet.union acc 
           (InvRelDiscriminationTree.retrieve_unifiables idx gty)
         in
         aux acc tl
       with Not_found -> aux acc tl
  in
    aux Ncic_termSet.empty c
;;
type cache_examination_result =
  [ `Failed_in of int
  | `UnderInspection 
  | `Succeded of NCic.term
  | `NotFound
  ]

type sort = T | P
type goal = int * sort (* goal, depth, sort *)
type fail = goal * cic_term
type candidate = int * Ast.term (* unique candidate number, candidate *)

type 'a op = 
  (* goal has to be proved *)
  | D of goal 
  (* goal has to be cached as a success obtained using candidate as the first
   * step *)
  | S of goal * (#tac_status as 'a)
         (* * cic_term * candidate (* int was minsize *) *)
  | L of goal * (#tac_status as 'a)

let pp_goal (g,_) = string_of_int g
let pp_item = function
  | D g -> "D" ^ pp_goal g
  | S (g,_) -> "S" ^ pp_goal g 
  | L (g,_) -> "L" ^ pp_goal g 

type flags = {
        do_types : bool; (* solve goals in Type *)
        maxwidth : int;
        maxsize  : int;
        maxdepth : int;
        timeout  : float;
}

type 'a tree_status = #tac_status as 'a * int * int
type 'a tree_item = 'a op

type 'a and_pos = 
        (AndOrTree.andT, 'a tree_status, 'a tree_item) AndOrTree.position
type 'a or_pos = 
        (AndOrTree.orT, 'a tree_status, 'a tree_item) AndOrTree.position

type 'a auto_status = 'a and_pos * th_cache

type 'a auto_result = 
  | Gaveup 
  | Proved of (#tac_status as 'a) * 'a auto_status option (* alt. proofs *)

let close_failures _ c = c;;
let prunable _ _ _ = false;;
let cache_examine cache gty = `Notfound;;
let put_in_subst s _ _ _  = s;;
let add_to_cache_and_del_from_orlist_if_green_cut _ _ c _ _ o f _ = c, o, f, false ;; 
let cache_add_underinspection c _ _ = c;;
let equational_case _ _ _ _ _ _ = [];;
let only _ _ _ = true;;

let candidate_no = ref 0;;

let sort_new_elems l = 
  List.sort (fun (_,_,_,_,l1) (_,_,_,_,l2) -> List.length l1 - List.length l2) l
;;

let try_candidate flags depth status t g =
 try
   debug_print ~depth (lazy ("try " ^ CicNotationPp.pp_term t));
   let status = NTactics.focus_tac [g] status in
   let status = NTactics.apply_tac ("",0,t) status in
   let open_goals = head_goals status#stack in
   debug_print ~depth
     (lazy ("success: "^String.concat " "(List.map string_of_int open_goals)));
   if List.length open_goals > flags.maxwidth || 
      (depth = flags.maxdepth && open_goals <> []) then
      (debug_print ~depth (lazy "pruned immediately"); None)
   else
     (incr candidate_no;
      Some ((!candidate_no,t),status,open_goals))
 with Error (msg,exn) -> debug_print ~depth (lazy "failed"); None
;;

let rec mk_irl n = function
  | [] -> []
  | _ :: tl -> NCic.Rel n :: mk_irl (n+1) tl
;;

let get_candidates status cache_th signature gty =
  let universe = status#auto_cache in
  let context = ctx_of gty in
  let _, raw_gty = term_of_cic_term status gty context in
  let cands = 
    NDiscriminationTree.DiscriminationTree.retrieve_unifiables universe raw_gty
  in
  let cands = 
    List.filter (only signature context) 
      (NDiscriminationTree.TermSet.elements cands)
  in
  List.map (fun t -> 
     let _status, t = term_of_cic_term status t context in Ast.NCic t) 
     (search_in_th gty cache_th)
  @ 
  List.map (function NCic.Const r -> Ast.NRef r | _ -> assert false) cands
;;

let applicative_case depth signature status flags g gty cache = 
  let candidates = get_candidates status cache signature gty in
  debug_print ~depth
    (lazy ("candidates: " ^ string_of_int (List.length candidates)));
  let elems = 
    List.fold_left 
      (fun elems cand ->
        match try_candidate flags depth status cand g with
        | None -> elems
        | Some x -> x::elems)
      [] candidates
  in
  elems
;;
let calculate_goal_ty (goalno,_) status = 
  try Some (get_goalty status goalno)
  with Error _ -> None
;;

let equational_and_applicative_case
  signature flags status g depth gty cache 
=
 let elems = 
  if false (*is_equational_case gty flags*) then
    let elems =
      equational_case
        signature status flags g gty cache 
    in
    let more_elems =
        applicative_case depth
          signature status flags g gty cache 
    in
      elems@more_elems
  else
    let elems =
      (*match LibraryObjects.eq_URI () with
      | Some _ ->
         smart_applicative_case dbd tables depth s fake_proof goalno 
           gty m context signature universe cache flags
      | None -> *)
         applicative_case depth
          signature status flags g gty cache 
    in
      elems
 in
 let elems = 
   List.map (fun c,s,gl -> 
       c,1,1,s,List.map (fun i -> 
                      let sort = 
                       match calculate_goal_ty (i,()) s with
                       | None -> assert false
                       | Some gty ->
                           let _, sort = typeof s (ctx_of gty) gty in
                           match term_of_cic_term s sort (ctx_of sort) with
                           | _, NCic.Sort NCic.Prop -> P
                           | _ -> (*T*)P
                      in
               i,sort) gl) elems 
 in
 let elems = sort_new_elems elems in
 elems, cache
;;


let d_goals l =
  let rec aux acc = function
    | (D g)::tl -> aux (acc@[g]) tl
    | (S _|L _)::tl -> aux acc tl
    | [] -> acc
  in
    aux [] l
;;
let prop_only l =
  List.filter (function (_,P) -> true | _ -> false) l
;;

let rec guess_name name ctx = 
  if name = "_" then guess_name "auto" ctx else
  if not (List.mem_assoc name ctx) then name else
  guess_name (name^"'") ctx
;;

let intro_case status gno gty depth cache name =
   let status = NTactics.focus_tac [gno] status in
   let status = NTactics.intro_tac (guess_name name (ctx_of gty)) status in
   let open_goals = head_goals status#stack in
   assert (List.length open_goals  = 1);
   let open_goal = List.hd open_goals in
   let ngty = get_goalty status open_goal in
   let ctx = ctx_of ngty in
   let t = mk_cic_term ctx (NCic.Rel 1) in
   let status, keys = keys_of_term status t in
   let cache = List.fold_left (add_to_th t) cache keys in
   debug_print ~depth (lazy ("intro: "^ string_of_int open_goal));
   incr candidate_no;
    (* XXX calculate the sort *)
   [(!candidate_no,Ast.Implicit `JustOne),0,0,status,[open_goal,P]],
   cache
;;
                      
let do_something signature flags s gno depth gty cache =
  let _s, raw_gty = term_of_cic_term s gty (ctx_of gty) in
  match raw_gty with
  | NCic.Prod (name,_,_) -> intro_case s gno gty depth cache name
  | _ -> 
      equational_and_applicative_case signature flags s gno depth gty cache
;;

module T = ZipTree
module Z = AndOrTree

let img_counter = ref 0 ;;
let show pos =
    incr img_counter;
    let file = ("/tmp/a"^string_of_int !img_counter^".dot") in
    debug_print (lazy("generating " ^ file));
    debug_do (fun () ->
    let oc = open_out file in
    let fmt = Format.formatter_of_out_channel oc in
    GraphvizPp.Dot.header fmt;
    Z.dump pp_item pos fmt;
    GraphvizPp.Dot.trailer fmt;
    Format.fprintf fmt "@?";
    close_out oc;
    ignore(Sys.command ("dot -Tpng "^file^" > "^file^".png")); 
    (*ignore(Sys.command ("eog "^file^".png"))*))
;;

let rightmost_bro pred pos =
 let rec last acc pos = 
   let acc = if pred pos then Some pos else acc in
   match Z.right pos with
   | None -> acc
   | Some pos -> last acc pos
 in
   last None pos
;;

let leftmost_bro pred pos =
 let rec fst pos = 
   if pred pos then Some pos else 
     match Z.right pos with
     | None ->  None
     | Some pos -> fst pos
 in
   fst pos
;;

let rec first_left_mark_L_as_D pred pos =
  if pred pos then 
      Some pos
  else 
    let pos = 
      match Z.getA pos with
      | s,L (g,_) -> 
           Z.inject T.Nil (Z.setA s (D g) pos)
      | _ -> pos
    in
    match Z.left pos with 
    | None -> None 
    | Some pos -> 
        first_left_mark_L_as_D pred pos
;;

let is_oS pos = 
 match Z.getO pos with
 | S _ -> true
 | D _ | L _ -> false
;;


let is_aS pos = 
 match Z.getA pos with
 | _,S _ -> true
 | _,D _ | _,L _ -> false
;;

let is_not_oS x = not (is_oS x);;
let is_not_aS x = not (is_aS x);;

let is_oL pos = match Z.getO pos with L _ -> true | _ -> false ;;
let is_aL pos = match Z.getA pos with _,L _ -> true | _ -> false ;;

let is_not_oL x = not (is_oL x) ;;
let is_not_aL x = not (is_aL x) ;;

let rec forall_left pred pos = 
  match Z.left pos with
  | None -> true
  | Some pos -> if pred pos then forall_left pred pos else false
;;

  
let rec product = function
  | [] -> []
  | ((g,s) :: tl) as l -> (s,List.map fst l) :: product tl
;;

let has_no_alternatives (pos : 'a and_pos) = 
  match Z.getA pos with
  | _, L _ -> true
  | _ -> false
;;

let rec collect_left_up (pos : 'a and_pos) =
  match Z.left pos with
  | Some pos -> 
     (match Z.getA pos with
     | _, L (g,s) -> (g,s) :: collect_left_up pos
     | _ -> [])
  | None -> 
      match Z.upA pos with
      | None -> [] (* root *)
      | Some pos -> collect_left_up (Z.upO pos)
;;

let compute_failed_goals (pos : 'a and_pos) =
  let curr = match Z.getA pos with (s,_,_),D g -> (g,s) | _ -> assert false in
  product (List.rev (curr :: collect_left_up pos) )
;;

let pp_failures l =
  debug_print (lazy("CACHE FAILURES/UNDERINSPECTION"));
  List.iter (fun (s,gl) -> 
    debug_print (lazy("FAIL: " ^
    String.concat " , " (List.map (fun g ->
    match calculate_goal_ty g s with
    | None -> 
        (try 
          let (i,_) = g in 
          let _,_,_,subst,_ = s#obj in
          let _,cc,_,ty = NCicUtils.lookup_subst i subst in
          let ty = mk_cic_term cc ty in
          string_of_int i^":"^ppterm s ty
        with NCicUtils.Subst_not_found _ -> "XXXX")
    | Some gty ->
       let s, gty = apply_subst s (ctx_of gty) gty in
       string_of_int (fst g)^":"^ppterm s gty) gl)))) 
    l
;;

let is_closed pos = 
  match Z.getA pos with
  | (s,_,_),S (g,_) 
  | (s,_,_),D g ->
      (match calculate_goal_ty g s with
      | None -> true
      | Some gty -> metas_of_term s gty = [])
  | _, L _ -> assert false
;;

let auto_main flags signature (pos : 'a and_pos) cache =
  let solved g depth size s (pos : 'a and_pos) =
    Z.inject (T.Node(`Or,[D g,T.Node(`And(s,depth,size),[])])) pos
  in
  let failed (pos : 'a and_pos) =
    pp_failures (compute_failed_goals pos);
    Z.inject (T.Node(`Or,[])) pos
  in

  let rec next ~unfocus (pos : 'a and_pos) cache = 
    (* TODO: process USER HINT is any *)
    match Z.downA pos with
    | Z.Unexplored -> attack pos cache (Z.getA pos)
    | Z.Alternatives pos -> nextO ~unfocus pos cache

  and nextO ~unfocus (pos : 'a or_pos) cache =
    match Z.getO pos with
    | S _ | L _ -> assert false (* XXX set to Nil when backtrack *)
    | D g -> 
        match Z.downO pos with
        | Z.Solution (s,_,_) -> move_solution_up ~unfocus true s pos cache 
        | Z.Todo pos -> next ~unfocus:true pos cache 

  and next_choice_point (pos : 'a and_pos) cache  =

    let rec global_choice_point (pos : 'a and_pos) : 'a auto_result =
(*             prerr_endline "global"; show pos; *)
      match Z.upA pos with
      | None -> Gaveup
      | Some alts -> 
          let alts = Z.inject T.Nil alts in
          let alts = 
            match Z.getO alts with
            | S (s,g) -> Z.setO (L (s,g)) alts 
            | D (g) -> Z.setO (L (g,Obj.magic g)) alts 
                       (* L (and other marks) for OR should have no arguments *)
            | L _ -> assert false
          in
          match Z.right alts with
          | None -> 
             let upalts = Z.upO alts in
             let upalts = Z.inject T.Nil upalts in
             let upalts = 
               match Z.getA upalts with
               | s,S (a,b) -> Z.setA s (L (a,b)) upalts 
               | _,L _ -> assert false
               | s,D (a) -> Z.setA s (L (a,Obj.magic a)) upalts 
             in
             backtrack upalts
          | Some pos -> 
              match Z.downO pos with
              | Z.Solution (s,_,_) -> 
                    move_solution_up ~unfocus:false true s pos cache
              | Z.Todo pos -> next ~unfocus:true pos cache 

    and backtrack (pos : 'a and_pos) : 'a auto_result =
(*             prerr_endline "backtrack"; show pos; *)
      let pos = Z.inject T.Nil pos in
      let pos = 
        match Z.getA pos with 
        | s,D g | s, S (g,_) | s,L(g,_) -> Z.setA s (D g) pos 
      in
      match first_left_mark_L_as_D is_aS pos with 
      | None -> global_choice_point pos
      | Some pos ->
         let rec local_choice_point pos =
(*             prerr_endline "local"; show pos; *)
           match Z.downA pos with
           | Z.Unexplored -> attack pos cache (Z.getA pos)
           | Z.Alternatives alts ->  
               match leftmost_bro is_not_oL alts with
               | None -> assert false (* is not L, thus has alternatives *)
               | Some pos ->
                   let is_D = is_not_oS pos in
                   match if is_D then Z.downO pos else Z.downOr pos with
                   | Z.Solution (s,_,_) -> assert(is_D);
                        move_solution_up ~unfocus:false true s pos cache
                   | Z.Todo pos when is_D -> attack pos cache (Z.getA pos)
                   | Z.Todo pos ->
                        match first_left_mark_L_as_D is_aS pos with
                        | Some pos -> local_choice_point pos
                        | None -> assert false
         in
           local_choice_point pos
    in
      backtrack pos

  and next_choice (pos : 'a and_pos) cache = 
    next_choice_point pos cache

  and move_solution_up 
      ~unfocus are_sons_L
      (status : #tac_status as 'a) (pos : 'a or_pos) cache 
  =
    let pos = (* mark as solved *)
      match Z.getO pos with
      | L _ -> assert false (* XXX  *) 
      | S (g,_) 
      | D g -> 
          if are_sons_L then 
             Z.inject T.Nil (Z.setO (L (g,status)) pos)
          else 
             Z.setO (S (g,status)) pos 
    in
    let has_alternative_or = match Z.right pos with None -> false | _ -> true in
    let pos = Z.upO pos in
    let are_all_lbro_L = forall_left is_aL pos in
    let has_no_alternative = 
      ((not has_alternative_or) && are_sons_L) ||
      is_closed pos
    in
    match Z.getA pos with
    | _, L _ -> assert false
    | (_, size, depth), S (g,_) 
       (* S if already solved and then solved again because of a backtrack *)
    | (_, size, depth), D g -> 
        let newg = 
          if has_no_alternative then (L (g,status)) else (S (g,status))in
        (* TODO: cache success g *)
        let pos = if has_no_alternative then Z.inject T.Nil pos else pos in
         let status = if unfocus then NTactics.unfocus_tac status else status
         in
        let news = status,size,depth in
        let pos = Z.setA news newg pos in
        match Z.right pos with
        | Some pos -> next ~unfocus:true pos cache
        | None -> 
            match Z.upA pos with
            | None -> Proved (status, Some (pos,cache))
            | Some pos -> 
               move_solution_up 
                 ~unfocus:true (has_no_alternative && are_all_lbro_L)
                 status pos cache 

  and attack pos cache and_item =
    (* show pos; uncomment to show the tree *)
    match and_item with
    | _, S _ -> assert false (* next would close the proof or give a D *) 
    | _, L _ -> assert false (* L is a final solution *)
    | (_, depth, _),_ when Unix.gettimeofday () > flags.timeout ->
        debug_print ~depth (lazy ("fail timeout"));
        Gaveup 
    | (s, depth, width), D (_, T as g) when not flags.do_types -> 
        debug_print ~depth (lazy "skip goal in Type");
        next ~unfocus:false (solved g depth width s pos) cache
    | (_,depth,_), D _ when depth > flags.maxdepth -> 
        debug_print ~depth (lazy "fail depth");
        next_choice (failed pos) cache
    | (_,depth,size), D _ when size > flags.maxsize -> 
        debug_print ~depth (lazy "fail size");
        next_choice (failed pos) cache
    | (s,depth,size), D (gno,_ as g) -> 
        assert (Z.eject pos = T.Nil); (*subtree must be unexplored *)
        match calculate_goal_ty g s with
        | None -> 
           debug_print ~depth (lazy("success side effect: "^string_of_int gno));
           next ~unfocus:false (solved g depth size s pos) cache
        | Some gty ->
           let s, gty = apply_subst s (ctx_of gty) gty in
           debug_print ~depth (lazy ("EXAMINE: "^ ppterm s gty));
           match cache_examine cache gty with
           | `Failed_in d when d <= depth -> 
               debug_print ~depth(lazy("fail depth (c): "^string_of_int gno));
               next_choice (failed pos) cache
           | `UnderInspection -> 
               debug_print ~depth (lazy("fail loop: "^string_of_int gno));
               next_choice (failed pos) cache
           | `Succeded t -> 
               debug_print ~depth (lazy("success (c): "^string_of_int gno));
               let s = put_in_subst s g t gty in
               next ~unfocus:true (solved g depth size s pos) cache
           | `Notfound 
           | `Failed_in _ -> 
               (* more depth than before or first time we see the goal *)
               if prunable s gty () then
                 (debug_print ~depth (lazy( "fail one father is equal"));
                  next_choice (failed pos) cache)
               else
               let cache = cache_add_underinspection cache gty depth in
               debug_print ~depth (lazy ("INSPECTING: " ^ 
                 string_of_int gno ^ "("^ string_of_int size ^ ") "));
               let subgoals, cache = 
                 do_something signature flags s gno depth gty cache
               in
               if subgoals = [] then (* this goal has failed *)
                 next_choice (failed pos) cache
               else
                 let size_gl l = List.length (prop_only l) in
                 let subtrees = 
                   List.map
                     (fun (_cand,depth_incr,size_mult,s,gl) ->
                       D(gno,P), 
                       T.Node (`And 
                          (s,depth+depth_incr,size+size_mult*(size_gl gl)), 
                               List.map (fun g -> D g,T.Nil) gl))
                     subgoals
                 in
                  next ~unfocus:true 
                    (Z.inject (T.Node (`Or,subtrees)) pos) cache
  in
    (next ~unfocus:true pos cache : 'a auto_result)
;;

let int name l def = 
  try int_of_string (List.assoc name l)
  with Failure _ | Not_found -> def
;;

let auto_tac ~params:(_univ,flags) status =
  let goals = head_goals status#stack in
  let status, cache = mk_th_cache status goals in
(*   pp_th status cache; *)
(*
  NDiscriminationTree.DiscriminationTree.iter status#auto_cache (fun p t -> 
    debug_print (lazy(
      NDiscriminationTree.NCicIndexable.string_of_path p ^ " |--> " ^
      String.concat "\n    " (List.map (
      NCicPp.ppterm ~metasenv:[] ~context:[] ~subst:[])
        (NDiscriminationTree.TermSet.elements t))
      )));
*)
  let depth = int "depth" flags 3 in 
  let size  = int "size" flags 10 in 
  let width = int "width" flags (3+List.length goals) in 
  (* XXX fix sort *)
  let goals = List.map (fun i -> D(i,P), T.Nil) goals in
  let elems = Z.start (T.Node (`And(status,0,0),goals)) in
  let signature = () in
  let flags = { 
          maxwidth = width;
          maxsize = size;
          maxdepth = depth;
          timeout = Unix.gettimeofday() +. 3000.;
          do_types = false; 
  } in
  let rec up_to x y =
    if x > y then raise (Error (lazy "auto gave up", None))
    else
      let _ = debug_print (lazy("\n\nRound "^string_of_int x^"\n")) in
      let flags = { flags with maxdepth = x } in
      match auto_main flags signature elems cache with
      | Gaveup -> up_to (x+1) y
      | Proved (s, _) -> 
          HLog.debug ("proved at depth " ^ string_of_int x);
          let stack = 
            match s#stack with
            | (g,t,k,f) :: rest -> (filter_open g,t,k,f):: rest
            | _ -> assert false
          in
          s#set_stack stack
  in
    up_to depth depth
;;

let rec rm_assoc n = function
  | [] -> assert false
  | (x,i)::tl when n=x -> i,tl
  | p::tl -> let i,tl = rm_assoc n tl in i,p::tl
;;

let merge canonicals elements n m =
  let cn,canonicals = rm_assoc n canonicals in
  let cm,canonicals = rm_assoc m canonicals in
  let ln,elements = rm_assoc cn elements in
  let lm,elements = rm_assoc cm elements in
  let canonicals = 
    (n,cm)::(m,cm)::List.map 
      (fun (x,xc) as p  -> 
	 if xc = cn then (x,cm) else p) canonicals
  in 
  let elements = (cn,ln@lm)::elements 
  in
    canonicals,elements
;;

let clusters f l =
  let canonicals = List.map (fun x -> (x,x)) l in
  let elements = List.map (fun x -> (x,[x])) l in
   List.fold_left 
     (fun (canonicals,elements) x ->
       let dep = f x in
	 List.fold_left 
	   (fun (canonicals,elements) d ->
	      merge canonicals elements d x) 
	   (canonicals,elements) dep)
     (canonicals,elements) l
;;

let group_by_tac ~eq_predicate ~action:tactic status = 
 let goals = head_goals status#stack in
 if List.length goals < 2 then tactic status 
 else
  let eq_predicate = eq_predicate status in
  let rec aux classes = function
    | [] -> classes
    | g :: tl ->
       try
         let c = List.find (fun c -> eq_predicate c g) classes in
         let classes = List.filter ((<>) c) classes in
         aux ((g::c) :: classes) tl
       with Not_found -> aux ([g] :: classes) tl
  in
  let classes = aux [] goals in
  List.iter 
   (fun l -> 
      HLog.debug ("cluster:" ^ String.concat "," (List.map string_of_int l)))
   classes;
  let pos_of l1 l2 = 
    let l2 = HExtlib.list_mapi (fun x i -> x,i+1) l2 in
    List.map (fun x -> List.assoc x l2) l1
  in
  NTactics.block_tac ([ NTactics.branch_tac ~force:false]
    @
    HExtlib.list_concat ~sep:[NTactics.shift_tac]
      (List.map (fun gl-> [NTactics.pos_tac (pos_of gl goals); tactic]) classes)
    @
    [ NTactics.merge_tac ]) status
;;

module IntSet = Set.Make(struct type t = int let compare = compare end)

let type_dependency status gl g =
  let rec closure acc = function
    | [] -> acc
    | x::l when IntSet.mem x acc -> closure acc l
    | x::l ->
        let acc = IntSet.add x acc in
        let gty = get_goalty status x in
        let deps = metas_of_term status gty in
        closure acc (deps @ l)
  in
  not (IntSet.is_empty 
        (IntSet.inter
          (closure IntSet.empty gl) 
          (closure IntSet.empty [g])))
;;

let auto_tac ~params = 
  group_by_tac ~eq_predicate:type_dependency ~action:(auto_tac ~params)
;;

(* ========================= dispatching of auto/auto_paramod ============ *)
let auto_tac ~params:(_,flags as params) ?trace_ref =
  if List.mem_assoc "paramodulation" flags then 
    auto_paramod_tac ~params 
  else if List.mem_assoc "demod" flags then 
    NnAuto.demod_tac ~params 
  else if List.mem_assoc "paramod" flags then 
    NnAuto.paramod_tac ~params 
  else if List.mem_assoc "fast_paramod" flags then 
    NnAuto.fast_eq_check_tac ~params  
  else if List.mem_assoc "slir" flags then 
    NnAuto.auto_tac ~params ?trace_ref
  else 
    auto_tac ~params
;;

(* EOF *)

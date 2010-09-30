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
 * http://cs.unibo.it/helm/.
 *)

(* let _profiler = <:profiler<_profiler>>;; *)

(* $Id$ *)

(* set to false to disable paramodulation inside auto_tac *)

let fst3 a,_,_ = a;;
let last _,_,a = a;;

let connect_to_auto = true;;

let debug_print = Utils.debug_print;;

(* profiling statistics... *)
let infer_time = ref 0.;;
let forward_simpl_time = ref 0.;;
let forward_simpl_new_time = ref 0.;;
let backward_simpl_time = ref 0.;;
let passive_maintainance_time = ref 0.;;

(* limited-resource-strategy related globals *)
let processed_clauses = ref 0;; (* number of equalities selected so far... *)
let time_limit = ref 0.;; (* in seconds, settable by the user... *)
let start_time = ref 0.;; (* time at which the execution started *)
let elapsed_time = ref 0.;;
(* let maximal_weight = ref None;; *)
let maximal_retained_equality = ref None;;

(* equality-selection related globals *)
let use_fullred = ref true;;
let weight_age_ratio = ref 6 (* 5 *);; (* settable by the user *)
let weight_age_counter = ref !weight_age_ratio ;;
let symbols_ratio = ref 0 (* 3 *);;
let symbols_counter = ref 0;;

(* non-recursive Knuth-Bendix term ordering by default *)
(* Utils.compare_terms := Utils.rpo;; *)
(* Utils.compare_terms := Utils.nonrec_kbo;; *)
(* Utils.compare_terms := Utils.ao;; *)

(* statistics... *)
let derived_clauses = ref 0;;
let kept_clauses = ref 0;;

(* varbiables controlling the search-space *)
let maxdepth = ref 3;;
let maxwidth = ref 3;;

type theorem = Cic.term * Cic.term * Cic.metasenv;;

let symbols_of_equality equality = 
  let (_, _, (_, left, right, _), _,_) = Equality.open_equality equality in
  let m1 = Utils.symbols_of_term left in
  let m = 
    Utils.TermMap.fold
      (fun k v res ->
         try
           let c = Utils.TermMap.find k res in
           Utils.TermMap.add k (c+v) res
         with Not_found ->
           Utils.TermMap.add k v res)
      (Utils.symbols_of_term right) m1
  in
  m
;;

(* griggio *)
module OrderedEquality = struct 
  type t = Equality.equality

  let compare eq1 eq2 =
    match Equality.meta_convertibility_eq eq1 eq2 with
    | true -> 0
    | false -> 
        let w1, _, (ty,left, right, _), m1,_ = Equality.open_equality eq1 in
        let w2, _, (ty',left', right', _), m2,_ = Equality.open_equality eq2 in
        match Pervasives.compare w1 w2 with
        | 0 -> 
            let res = (List.length m1) - (List.length m2) in 
            if res <> 0 then res else 
              Equality.compare eq1 eq2
        | res -> res 
end 

module EqualitySet = Set.Make(OrderedEquality);;

type passive_table = Equality.equality list * EqualitySet.t * Indexing.Index.t
type active_table = Equality.equality list * Indexing.Index.t
type new_proof = 
  Equality.goal_proof * Equality.proof * int * Subst.substitution * Cic.metasenv
type result =
  | ParamodulationFailure of 
      string * active_table * passive_table * Equality.equality_bag
  | ParamodulationSuccess of 
      new_proof * active_table * passive_table * Equality.equality_bag
;;

let list_of_passive (l,_,_) = l ;;
let list_of_active (l,_) = l ;;

let make_passive eq_list =
  let set =
    List.fold_left (fun s e -> EqualitySet.add e s) EqualitySet.empty eq_list
  in
  (* we have the invariant that the list and the set have the same
   * cardinality *)
  EqualitySet.elements set, set,  
  List.fold_left Indexing.index Indexing.empty eq_list
;;

let make_empty_active () = [], Indexing.empty ;;
let make_active eq_list = 
  eq_list, List.fold_left Indexing.index Indexing.empty eq_list
;;

let size_of_passive (passive_list, _,_) = List.length passive_list;;
let size_of_active (active_list, _) = List.length active_list;;

let passive_is_empty = function
  | [], s , _ when EqualitySet.is_empty s -> true
  | [], s ,_ -> assert false (* the set and the list should be in sync *)
  | _ -> false
;;

type goals = Equality.goal list * Equality.goal list

let no_more_passive_goals g = match g with | _,[] -> true | _ -> false;;
  

let age_factor = 0.01;;

(**
   selects one equality from passive. The selection strategy is a combination
   of weight, age and goal-similarity
*)

let rec select env g passive =
  processed_clauses := !processed_clauses + 1;
(*
  let goal =
    match (List.rev goals) with goal::_ -> goal | _ -> assert false
  in
*)
  let pos_list, pos_set, pos_table = passive in
  let remove eq l = List.filter (fun e -> Equality.compare e eq <> 0) l in
  if !weight_age_ratio > 0 then
    weight_age_counter := !weight_age_counter - 1;
  match !weight_age_counter with
  | 0 -> (
      weight_age_counter := !weight_age_ratio;
      let skip_giant pos_list pos_set pos_table =
        match pos_list with
          | (hd:EqualitySet.elt)::tl ->
              let w,_,_,_,_ = Equality.open_equality hd in
                if w < 30 then
                  hd, (tl, EqualitySet.remove hd pos_set, 
                           Indexing.remove_index pos_table hd)
                else
(*
                  (prerr_endline 
                    ("+++ skipping giant of size "^string_of_int w^" +++");
*)
                  select env g (tl@[hd],pos_set,pos_table)
          | _ -> assert false
		   in
		    skip_giant pos_list pos_set pos_table)

(*
      let rec skip_giant pos_list pos_set =
        match pos_list with
          | (hd:EqualitySet.elt)::tl ->
              let w,_,_,_,_ = Equality.open_equality hd in
              let pos_set = EqualitySet.remove hd pos_set in
                if w < 30 then
                  hd, (tl, pos_set)
                else
                  (prerr_endline 
                    ("+++ skipping giant of size "^string_of_int w^" +++");
                  skip_giant tl pos_set)
          | _ -> assert false
      in        
  skip_giant pos_list pos_set)

*)
(*
  | _ when (!symbols_counter > 0) -> 
     (symbols_counter := !symbols_counter - 1;
      let cardinality map =
        Utils.TermMap.fold (fun k v res -> res + v) map 0
      in
      let symbols =
        let _, _, term = goal in
        Utils.symbols_of_term term
      in
      let card = cardinality symbols in
      let foldfun k v (r1, r2) = 
        if Utils.TermMap.mem k symbols then
          let c = Utils.TermMap.find k symbols in
          let c1 = abs (c - v) in
          let c2 = v - c1 in
          r1 + c2, r2 + c1
        else
          r1, r2 + v
      in
      let f equality (i, e) =
        let common, others =
          Utils.TermMap.fold foldfun (symbols_of_equality equality) (0, 0)
        in
        let c = others + (abs (common - card)) in
        if c < i then (c, equality)
        else (i, e)
      in
      let e1 = EqualitySet.min_elt pos_set in
      let initial =
        let common, others = 
          Utils.TermMap.fold foldfun (symbols_of_equality e1) (0, 0)
        in
        (others + (abs (common - card))), e1
      in
      let _, current = EqualitySet.fold f pos_set initial in
        current,
      (remove current pos_list, EqualitySet.remove current pos_set))
*)
  | _ ->
      symbols_counter := !symbols_ratio;
      let my_min e1 e2 =
        let w1,_,_,_,_ = Equality.open_equality e1 in
        let w2,_,_,_,_ = Equality.open_equality e2 in
        if w1 < w2 then e1 else e2
      in
      let rec my_min_elt min = function
        | [] -> min
        | hd::tl -> my_min_elt (my_min hd min) tl
      in
(*     let current = EqualitySet.min_elt pos_set in  *)
       let current = my_min_elt (List.hd pos_list) (List.tl pos_list) in 
       current,(remove current pos_list, EqualitySet.remove current pos_set,
	       Indexing.remove_index pos_table current)
;;


let filter_dependent bag passive id =
  let pos_list, pos_set, pos_table = passive in
  let passive,no_pruned =
    List.fold_right
      (fun eq ((list,set,table),no) ->
         if Equality.depend bag eq id then
           (list, EqualitySet.remove eq set,Indexing.remove_index table eq), 
	    no + 1
         else 
           (eq::list,set,table), no)
      pos_list (([],pos_set,pos_table),0)
  in
(*
  if no_pruned > 0 then
    prerr_endline ("+++ pruning "^ string_of_int no_pruned ^" passives +++");  
*)
  passive
;;


(* adds to passive a list of equalities new_pos *)
let add_to_passive passive new_pos preferred =
  let pos_list, pos_set , pos_table = passive in
  let ok set equality = not (EqualitySet.mem equality set) in
  let pos = List.filter (ok pos_set) new_pos in
  let add set equalities =
    List.fold_left (fun s e -> EqualitySet.add e s) set equalities
  in
  let pos_head, pos_tail =
    List.partition 
      (fun e -> List.exists (fun x -> Equality.compare x e = 0) preferred)  
      pos 
  in
  pos_head @ pos_list @ pos_tail, add pos_set pos,
   List.fold_left Indexing.index pos_table pos
;;

(* TODO *)
(* removes from passive equalities that are estimated impossible to activate
   within the current time limit *)
let prune_passive howmany (active, _) passive =
  let (pl, ps), tbl = passive in
  let howmany = float_of_int howmany
  and ratio = float_of_int !weight_age_ratio in
  let round v =
    let t = ceil v in 
    int_of_float (if t -. v < 0.5 then t else v)
  in
  let in_weight = round (howmany *. ratio /. (ratio +. 1.))
  and in_age = round (howmany /. (ratio +. 1.)) in 
  Utils.debug_print
    (lazy (Printf.sprintf "in_weight: %d, in_age: %d\n" in_weight in_age));
  let counter = ref !symbols_ratio in
  let rec pickw w ps =
    if w > 0 then
      if !counter > 0 then
        let _ =
          counter := !counter - 1;
          if !counter = 0 then counter := !symbols_ratio in
        let e = EqualitySet.min_elt ps in
        let ps' = pickw (w-1) (EqualitySet.remove e ps) in
          EqualitySet.add e ps'
      else
        let e = EqualitySet.min_elt ps in
        let ps' = pickw (w-1) (EqualitySet.remove e ps) in
        EqualitySet.add e ps'        
    else
      EqualitySet.empty
  in
  let ps = pickw in_weight ps in
  let rec picka w s l =
    if w > 0 then
      match l with
      | [] -> w, s, []
      | hd::tl when not (EqualitySet.mem hd s) ->
          let w, s, l = picka (w-1) s tl in
          w, EqualitySet.add hd s, hd::l
      | hd::tl ->
          let w, s, l = picka w s tl in
          w, s, hd::l
    else
      0, s, l
  in
  let _, ps, pl = picka in_age ps pl in
  if not (EqualitySet.is_empty ps) then
    maximal_retained_equality := Some (EqualitySet.max_elt ps); 
  let tbl =
    EqualitySet.fold
      (fun e tbl -> Indexing.index tbl e) ps Indexing.empty
  in
  (pl, ps), tbl  
;;


(** inference of new equalities between current and some in active *)
let infer bag eq_uri env current (active_list, active_table) =
  let (_,c,_) = env in 
  if Utils.debug_metas then
    (ignore(Indexing.check_target bag c current "infer1");
     ignore(List.map (function current -> Indexing.check_target bag c current "infer2") active_list)); 
  let bag, new_pos = 
      let bag, copy_of_current = Equality.fix_metas bag current in
      let active_table =  Indexing.index active_table copy_of_current in
(*       let _ = <:start<current contro active>> in *)
      let bag, res =
        Indexing.superposition_right bag eq_uri env active_table current 
      in
(*       let _ = <:stop<current contro active>> in *)
      if Utils.debug_metas then
        ignore(List.map 
                 (function current -> 
                    Indexing.check_target bag c current "sup0") res);
      let rec infer_positive bag table = function
        | [] -> bag, []
        | equality::tl ->
            let bag, res =
              Indexing.superposition_right bag 
                ~subterms_only:true eq_uri env table equality 
            in
              if Utils.debug_metas then
                ignore
                  (List.map 
                     (function current -> 
                        Indexing.check_target bag c current "sup2") res);
              let bag, pos = infer_positive bag table tl in
              bag, res @ pos
      in
      let curr_table = Indexing.index Indexing.empty current in
      let bag, pos = infer_positive bag curr_table ((*copy_of_current::*)active_list) in
      if Utils.debug_metas then 
        ignore(List.map 
                 (function current -> 
                    Indexing.check_target bag c current "sup3") pos);
      bag, res @ pos
  in
  derived_clauses := !derived_clauses + (List.length new_pos);
  match !maximal_retained_equality with
    | None -> bag, new_pos
    | Some eq ->
      ignore(assert false);
      (* if we have a maximal_retained_equality, we can discard all equalities
         "greater" than it, as they will never be reached...  An equality is
         greater than maximal_retained_equality if it is bigger
         wrt. OrderedEquality.compare and it is less similar than
         maximal_retained_equality to the current goal *)
        bag, List.filter (fun e -> OrderedEquality.compare e eq <= 0) new_pos
;;

let check_for_deep_subsumption env active_table eq =
  let _,_,(eq_ty, left, right, order),metas,id = Equality.open_equality eq in
  let check_subsumed deep l r = 
    let eqtmp = 
      Equality.mk_tmp_equality(0,(eq_ty,l,r,Utils.Incomparable),metas)in
    match Indexing.subsumption env active_table eqtmp with
    | None -> false
    | Some _ -> true        
  in 
  let rec aux b (ok_so_far, subsumption_used) t1 t2  = 
    match t1,t2 with
      | t1, t2 when not ok_so_far -> ok_so_far, subsumption_used
      | t1, t2 when subsumption_used -> t1 = t2, subsumption_used
      | Cic.Appl (h1::l),Cic.Appl (h2::l') ->
          let rc = check_subsumed b t1 t2 in 
            if rc then 
              true, true
            else if h1 = h2 then
              (try 
                 List.fold_left2 
                   (fun (ok_so_far, subsumption_used) t t' -> 
                      aux true (ok_so_far, subsumption_used) t t')
                   (ok_so_far, subsumption_used) l l'
               with Invalid_argument _ -> false,subsumption_used)
            else
              false, subsumption_used
    | _ -> false, subsumption_used 
  in
  fst (aux false (true,false) left right)
;;

(** simplifies current using active and passive *)
let forward_simplify bag eq_uri env current (active_list, active_table) =
  let _, context, _ = env in
  let demodulate bag table current = 
    let bag, newcurrent =
      Indexing.demodulation_equality bag eq_uri env table current
    in
    bag, if Equality.is_identity env newcurrent then None else Some newcurrent
  in
  let demod bag current =
    if Utils.debug_metas then
      ignore (Indexing.check_target bag context current "demod0");
    let bag, res = demodulate bag active_table current in
    if Utils.debug_metas then
      ignore ((function None -> () | Some x -> 
      ignore (Indexing.check_target bag context x "demod1");()) res);
    bag, res
  in 
  let bag, res = demod bag current in
  match res with
  | None -> bag, None
  | Some c ->
      if Indexing.in_index active_table c ||
         check_for_deep_subsumption env active_table c 
      then
        bag, None
      else 
        bag, res
;;

(** simplifies new using active and passive *)
let forward_simplify_new bag eq_uri env new_pos active =
  if Utils.debug_metas then
    begin
      let m,c,u = env in
        ignore(List.map 
        (fun current -> Indexing.check_target bag c current "forward new pos") 
      new_pos;)
    end;
  let active_list, active_table = active in
  let demodulate bag table target =
    let bag, newtarget =
      Indexing.demodulation_equality bag eq_uri env table target 
    in
    bag, newtarget
  in
  (* we could also demodulate using passive. Currently we don't *)
  let bag, new_pos = 
    List.fold_right (fun x (bag,acc) -> 
       let bag, y = demodulate bag active_table x in
       bag, y::acc) 
    new_pos (bag,[])
  in
  let new_pos_set =
    List.fold_left
      (fun s e ->
         if not (Equality.is_identity env e) then
           EqualitySet.add e s
         else s)
      EqualitySet.empty new_pos
  in
  let new_pos = EqualitySet.elements new_pos_set in
  let subs e = Indexing.subsumption env active_table e = None in
  let is_duplicate e = not (Indexing.in_index active_table e) in
  bag, List.filter subs (List.filter is_duplicate new_pos)
;;


(** simplifies a goal with equalities in active and passive *)  
let rec simplify_goal bag env goal (active_list, active_table) =
  let demodulate table goal = Indexing.demodulation_goal bag env table goal in
  let changed, goal = demodulate active_table goal in
  changed,
  if not changed then 
    goal 
  else 
    snd (simplify_goal bag env goal (active_list, active_table)) 
;;


let simplify_goals bag env goals active =
  let a_goals, p_goals = goals in
  let p_goals = List.map (fun g -> snd (simplify_goal bag env g active)) p_goals in
  let a_goals = List.map (fun g -> snd (simplify_goal bag env g active)) a_goals in
  a_goals, p_goals
;;


(** simplifies active usign new *)
let backward_simplify_active 
  bag eq_uri env new_pos new_table min_weight active 
=
  let active_list, active_table = active in
  let bag, active_list, newa, pruned = 
    List.fold_right
      (fun equality (bag, res, newn,pruned) ->
         let ew, _, _, _,id = Equality.open_equality equality in
         if ew < min_weight then
           bag, equality::res, newn,pruned
         else
           match 
             forward_simplify bag eq_uri env equality (new_pos, new_table) 
           with
           | bag, None -> bag, res, newn, id::pruned
           | bag, Some e ->
               if Equality.compare equality e = 0 then
                 bag, e::res, newn, pruned
               else 
                 bag, res, e::newn, pruned)
      active_list (bag, [], [],[])
  in
  let find eq1 where =
    List.exists (Equality.meta_convertibility_eq eq1) where
  in
  let id_of_eq eq = 
    let _, _, _, _,id = Equality.open_equality eq in id
  in
  let ((active1,pruned),tbl), newa =
    List.fold_right
      (fun eq ((res,pruned), tbl) ->
         if List.mem eq res then
           (res, (id_of_eq eq)::pruned),tbl 
         else if (Equality.is_identity env eq) || (find eq res) then (
           (res, (id_of_eq eq)::pruned),tbl
         ) 
         else
           (eq::res,pruned), Indexing.index tbl eq)
      active_list (([],pruned), Indexing.empty),
    List.fold_right
      (fun eq p ->
         if (Equality.is_identity env eq) then p
         else eq::p)
      newa []
  in
  match newa with
  | [] -> bag, (active1,tbl), None, pruned 
  | _ -> bag, (active1,tbl), Some newa, pruned
;;


(** simplifies passive using new *)
let backward_simplify_passive 
  bag eq_uri env new_pos new_table min_weight passive 
=
  let (pl, ps), passive_table = passive in
  let f bag equality (resl, ress, newn) =
    let ew, _, _, _ , _ = Equality.open_equality equality in
    if ew < min_weight then
      bag, (equality::resl, ress, newn)
    else
      match 
        forward_simplify bag eq_uri env equality (new_pos, new_table) 
      with
      | bag, None -> 
          bag, (resl, EqualitySet.remove equality ress, newn)
      | bag, Some e ->
          if equality = e then
            bag, (equality::resl, ress, newn)
          else
            let ress = EqualitySet.remove equality ress in
            bag, (resl, ress, e::newn)
  in
  let bag, (pl, ps, newp) = 
    List.fold_right (fun x (bag,acc) -> f bag x acc) pl (bag,([], ps, [])) in
  let passive_table =
    List.fold_left
      (fun tbl e -> Indexing.index tbl e) Indexing.empty pl
  in
  match newp with
  | [] -> bag, ((pl, ps), passive_table), None
  |  _ -> bag, ((pl, ps), passive_table), Some (newp)
;;

let build_table equations =
    List.fold_left
      (fun (l, t, w) e ->
         let ew, _, _, _ , _ = Equality.open_equality e in
         e::l, Indexing.index t e, min ew w)
      ([], Indexing.empty, 1000000) equations
;;
  

let backward_simplify bag eq_uri env new' active =
  let new_pos, new_table, min_weight = build_table new' in
  let bag, active, newa, pruned =
    backward_simplify_active bag eq_uri env new_pos new_table min_weight active 
  in
  bag, active, newa, pruned
;;

let close bag eq_uri env new' given =
  let new_pos, new_table, min_weight =
    List.fold_left
      (fun (l, t, w) e ->
         let ew, _, _, _ , _ = Equality.open_equality e in
         e::l, Indexing.index t e, min ew w)
      ([], Indexing.empty, 1000000) (snd new')
  in
  List.fold_left
    (fun (bag,p) c ->
       let bag, pos = infer bag eq_uri env c (new_pos,new_table) in
       bag, pos@p)
    (bag,[]) given 
;;

let is_commutative_law eq =
  let w, proof, (eq_ty, left, right, order), metas , _ = 
    Equality.open_equality eq 
  in
    match left,right with
        Cic.Appl[f1;Cic.Meta _ as a1;Cic.Meta _ as b1], 
        Cic.Appl[f2;Cic.Meta _ as a2;Cic.Meta _ as b2] ->
          f1 = f2 && a1 = b2 && a2 = b1
      | _ -> false
;;

let prova bag eq_uri env new' active = 
  let given = List.filter is_commutative_law (fst active) in
  let _ =
    Utils.debug_print
      (lazy
         (Printf.sprintf "symmetric:\n%s\n"
            (String.concat "\n"
               (List.map
                  (fun e -> Equality.string_of_equality ~env e)
                   given)))) in
    close bag eq_uri env new' given
;;

(* returns an estimation of how many equalities in passive can be activated
   within the current time limit *)
let get_selection_estimate () =
  elapsed_time := (Unix.gettimeofday ()) -. !start_time;
  (*   !processed_clauses * (int_of_float (!time_limit /. !elapsed_time)) *)
  int_of_float (
    ceil ((float_of_int !processed_clauses) *.
            ((!time_limit (* *. 2. *)) /. !elapsed_time -. 1.)))
;;


(** initializes the set of goals *)
let make_goals goal =
  let active = []
  and passive = [0, [goal]] in
  active, passive
;;

let make_goal_set goal = 
  ([],[goal]) 
;;

(** initializes the set of theorems *)
let make_theorems theorems =
  theorems, []
;;


let activate_goal (active, passive) =
  if active = [] then
    match passive with
    | goal_conj::tl -> true, (goal_conj::active, tl)
    | [] -> false, (active, passive)
  else  
    true, (active,passive)
;;


let activate_theorem (active, passive) =
  match passive with
  | theorem::tl -> true, (theorem::active, tl)
  | [] -> false, (active, passive)
;;

let rec simpl bag eq_uri env e others others_simpl =
  let active = others @ others_simpl in
  let tbl =
    List.fold_left
      (fun t e -> 
         if Equality.is_identity env e then t else Indexing.index t e) 
      Indexing.empty active
  in
  let bag, res = 
    forward_simplify bag eq_uri env e (active, tbl) 
  in
    match others with
      | hd::tl -> (
          match res with
            | None -> simpl bag eq_uri env hd tl others_simpl
            | Some e -> simpl bag eq_uri env hd tl (e::others_simpl)
        )
      | [] -> (
          match res with
            | None -> bag, others_simpl
            | Some e -> bag, e::others_simpl
        )
;;

let simplify_equalities bag eq_uri env equalities =
  Utils.debug_print
    (lazy 
       (Printf.sprintf "equalities:\n%s\n"
          (String.concat "\n"
             (List.map Equality.string_of_equality equalities))));
Utils.debug_print (lazy "SIMPLYFYING EQUALITIES...");
  match equalities with
    | [] -> bag, []
    | hd::tl ->
        let bag, res = simpl bag eq_uri env hd tl [] in
        let res = List.rev res in
          Utils.debug_print
            (lazy
               (Printf.sprintf "equalities AFTER:\n%s\n"
                  (String.concat "\n"
                     (List.map Equality.string_of_equality res))));
       bag, res
;;

let print_goals goals = 
  (String.concat "\n"
     (List.map
        (fun (d, gl) ->
           let gl' =
             List.map
               (fun (p, _, t) ->
                  (* (string_of_proof p) ^ ", " ^ *) (CicPp.ppterm t)) gl
           in
           Printf.sprintf "%d: %s" d (String.concat "; " gl')) goals))
;;
              
let pp_goal_set msg goals names = 
  let active_goals, passive_goals = goals in
  debug_print (lazy ("////" ^ msg));
  debug_print (lazy ("ACTIVE G: " ^
    (String.concat "\n " (List.map (fun (_,_,g) -> CicPp.pp g names)
    active_goals))));
  debug_print (lazy ("PASSIVE G: " ^
    (String.concat "\n " (List.map (fun (_,_,g) -> CicPp.pp g names)
    passive_goals))))
;;

let check_if_goal_is_subsumed bag ((_,ctx,_) as env) table (goalproof,menv,ty) =
(*   let names = Utils.names_of_context ctx in *)
  match ty with
  | Cic.Appl[Cic.MutInd(uri,_,_);eq_ty;left;right] 
    when LibraryObjects.is_eq_URI uri ->
      (let bag, goal_equation = 
         Equality.mk_equality bag
           (0,Equality.Exact (Cic.Implicit None),(eq_ty,left,right,Utils.Eq),menv) 
      in
       (* match Indexing.subsumption env table goal_equation with *)
       match Indexing.unification env table goal_equation with 
        | Some (subst, equality, swapped ) ->
(*
            prerr_endline 
             ("GOAL SUBSUMED IS: "^Equality.string_of_equality goal_equation ~env);
            prerr_endline 
             ("GOAL IS SUBSUMED BY: "^Equality.string_of_equality equality ~env);
            prerr_endline ("SUBST:"^Subst.ppsubst ~names subst);
*)
            let (_,p,(ty,l,r,_),m,id) = Equality.open_equality equality in
            let cicmenv = Subst.apply_subst_metasenv subst (m @ menv) in
            let bag, p =
              if swapped then
                Equality.symmetric bag eq_ty l id uri m
              else
                bag, p
            in
            bag, Some (goalproof, p, id, subst, cicmenv)
        | None -> 
                        bag, None)
  | _ -> bag, None
;;

let find_all_subsumed bag env table (goalproof,menv,ty) =
  match ty with
  | Cic.Appl[Cic.MutInd(uri,_,_);eq_ty;left;right] 
    when LibraryObjects.is_eq_URI uri ->
      let bag, goal_equation = 
        (Equality.mk_equality bag
          (0,Equality.Exact (Cic.Implicit None),(eq_ty,left,right,Utils.Eq),menv)) 
      in
      List.fold_right
	  (fun (subst, equality, swapped) (bag,acc) ->
	     let (_,p,(ty,l,r,_),m,id) = Equality.open_equality equality in
             let cicmenv = Subst.apply_subst_metasenv subst (m @ menv) in
             if Utils.debug_metas then
               Indexing.check_for_duplicates cicmenv "from subsumption";
             let bag, p =
	       if swapped then
                 Equality.symmetric bag eq_ty l id uri m
	       else
                 bag, p
             in 
              bag, (goalproof, p, id, subst, cicmenv)::acc)
         (Indexing.subsumption_all env table goal_equation) (bag,[])
	  (* (Indexing.unification_all env table goal_equation) *)
  | _ -> assert false
;;


let check_if_goal_is_identity env = function
  | (goalproof,m,Cic.Appl[Cic.MutInd(uri,_,ens);eq_ty;left;right]) 
    when left = right && LibraryObjects.is_eq_URI uri ->
      let reflproof = Equality.Exact (Equality.refl_proof uri eq_ty left) in
      Some (goalproof, reflproof, 0, Subst.empty_subst,m)
  | (goalproof,m,Cic.Appl[Cic.MutInd(uri,_,ens);eq_ty;left;right]) 
    when LibraryObjects.is_eq_URI uri ->
    (let _,context,_ = env in
    try 
     let s,m,_ = 
       Founif.unification [] m context left right CicUniv.empty_ugraph 
     in
      let reflproof = Equality.Exact (Equality.refl_proof uri eq_ty left) in
      let m = Subst.apply_subst_metasenv s m in
      Some (goalproof, reflproof, 0, s,m)
    with CicUnification.UnificationFailure _ -> None)
  | _ -> None
;;                              
    
let rec check b goal = function
  | [] -> b, None
  | f::tl ->
      match f b goal with
      | b, None -> check b goal tl
      | b, (Some _ as ok)  -> b, ok
;;
  
let simplify_goal_set bag env goals active = 
  let active_goals, passive_goals = goals in 
  let find (_,_,g) where =
    List.exists (fun (_,_,g1) -> Equality.meta_convertibility g g1) where
  in
    (* prova:tengo le passive semplificate 
  let passive_goals = 
    List.map (fun g -> snd (simplify_goal env g active)) passive_goals 
  in *)
    List.fold_left
      (fun (acc_a,acc_p) goal -> 
        match simplify_goal bag env goal active with 
        | changed, g -> 
            if changed then 
              if find g acc_p then acc_a,acc_p else acc_a,g::acc_p
            else
              if find g acc_a then acc_a,acc_p else g::acc_a,acc_p)
      ([],passive_goals) active_goals
;;

let check_if_goals_set_is_solved bag env active passive goals =
  let active_goals, passive_goals = goals in
  List.fold_left 
    (fun (bag, proof) goal ->
      match proof with
      | Some p -> bag, proof
      | None -> 
          check bag goal [
            (fun b x -> b, check_if_goal_is_identity env x);
            (fun bag -> check_if_goal_is_subsumed bag env (snd active));
            (fun bag -> check_if_goal_is_subsumed bag env (last passive))
             ])
    (bag,None) (active_goals @ passive_goals)
;;

let infer_goal_set bag env active goals = 
  let active_goals, passive_goals = goals in
  let rec aux bag = function
    | [] -> bag, (active_goals, [])
    | hd::tl ->
        let changed, selected = simplify_goal bag env hd active in
        let (_,m1,t1) = selected in
        let already_in = 
          List.exists (fun (_,_,t) -> Equality.meta_convertibility t t1) 
              active_goals
        in
        if already_in then 
             aux bag tl 
          else
            let passive_goals = tl in
            let bag, new_passive_goals =
              if Utils.metas_of_term t1 = [] then 
                bag, passive_goals
              else 
                let bag, new' = 
                   Indexing.superposition_left bag env (snd active) selected
                in
                bag, passive_goals @ new'
            in
            bag, (selected::active_goals, new_passive_goals)
  in 
   aux bag passive_goals
;;

let infer_goal_set_with_current bag env current goals active = 
  let active_goals, passive_goals = simplify_goal_set bag env goals active in
  let l,table,_  = build_table [current] in
  let bag, passive_goals = 
   List.fold_left 
    (fun (bag, acc) g ->
      let bag, new' = Indexing.superposition_left bag env table g in
      bag, acc @ new')
    (bag, passive_goals) active_goals
  in
  bag, active_goals, passive_goals
;;

let ids_of_goal g = 
  let p,_,_ = g in
  let ids = List.map (fun _,_,i,_,_ -> i) p in
  ids
;;

let ids_of_goal_set (ga,gp) =
  List.flatten (List.map ids_of_goal ga) @
  List.flatten (List.map ids_of_goal gp)
;;

let size_of_goal_set_a (l,_) = List.length l;;
let size_of_goal_set_p (_,l) = List.length l;;
      
let pp_goals label goals context = 
  let names = Utils.names_of_context context in
  List.iter                 
    (fun _,_,g -> 
      debug_print (lazy 
        (Printf.sprintf  "Current goal: %s = %s\n" label (CicPp.pp g names))))
    (fst goals);
  List.iter                 
    (fun _,_,g -> 
      debug_print (lazy 
        (Printf.sprintf  "PASSIVE goal: %s = %s\n" label (CicPp.pp g names))))
      (snd goals);
;;

let print_status iterno goals active passive =
  debug_print (lazy 
    (Printf.sprintf "\n%d #ACTIVES: %d #PASSIVES: %d #GOALSET: %d(%d)"
      iterno (size_of_active active) (size_of_passive passive)
      (size_of_goal_set_a goals) (size_of_goal_set_p goals)))
;;

let add_to_active_aux bag active passive env eq_uri current =
  debug_print (lazy ("Adding to actives : " ^ 
    Equality.string_of_equality ~env  current));
  match forward_simplify bag eq_uri env current active with
  | bag, None -> None, active, passive, bag
  | bag, Some current ->
      let bag, new' = infer bag eq_uri env current active in
      let active = 
        let al, tbl = active in
        al @ [current], Indexing.index tbl current
      in
      let rec simplify bag new' active passive =
        let bag, new' = 
          forward_simplify_new bag eq_uri env new' active 
        in
        let bag, active, newa, pruned =
          backward_simplify bag eq_uri env new' active 
        in
        let passive = 
          List.fold_left (filter_dependent bag) passive pruned 
        in
        match newa with
        | None -> bag, active, passive, new'
        | Some p -> simplify bag (new' @ p) active passive 
      in
      let bag, active, passive, new' = 
        simplify bag new' active passive
      in
      let passive = add_to_passive passive new' [] in
      Some new', active, passive, bag
;;

(** given-clause algorithm with full reduction strategy: NEW implementation *)
(* here goals is a set of goals in OR *)
let given_clause 
  bag eq_uri ((_,context,_) as env) goals passive active 
  goal_steps saturation_steps max_time
= 
  let initial_time = Unix.gettimeofday () in
  let iterations_left iterno = 
    let now = Unix.gettimeofday () in
    let time_left = max_time -. now in
    let time_spent_until_now = now -. initial_time in
    let iteration_medium_cost = 
      time_spent_until_now /. (float_of_int iterno)
    in
    let iterations_left = time_left /. iteration_medium_cost in
    int_of_float iterations_left 
  in
  let rec step bag goals passive active g_iterno s_iterno =
    if g_iterno > goal_steps && s_iterno > saturation_steps then
      (ParamodulationFailure ("No more iterations to spend",active,passive,bag))
    else if Unix.gettimeofday () > max_time then
      (ParamodulationFailure ("No more time to spend",active,passive,bag))
    else
      let _ = 
         print_status (max g_iterno s_iterno) goals active passive  
(*         Printf.eprintf ".%!"; *)
      in
      (* PRUNING OF PASSIVE THAT WILL NEVER BE PROCESSED *) 
      let passive =
        let selection_estimate = iterations_left (max g_iterno s_iterno) in
        let kept = size_of_passive passive in
        if kept > selection_estimate then 
          begin
            (*Printf.eprintf "Too many passive equalities: pruning...";
            prune_passive selection_estimate active*) passive
          end
        else
          passive
      in
      kept_clauses := (size_of_passive passive) + (size_of_active active);
      let bag, goals = 
        if g_iterno < goal_steps then
          infer_goal_set bag env active goals 
        else
          bag, goals
      in
      match check_if_goals_set_is_solved bag env active passive goals with
      | bag, Some p -> 
          debug_print (lazy 
            (Printf.sprintf "\nFound a proof in: %f\n" 
              (Unix.gettimeofday() -. initial_time)));
          ParamodulationSuccess (p,active,passive,bag)
      | bag, None -> 
          (* SELECTION *)
          if passive_is_empty passive then
            if no_more_passive_goals goals then 
              ParamodulationFailure 
                ("No more passive equations/goals",active,passive,bag)
              (*maybe this is a success! *)
            else
              step bag goals passive active (g_iterno+1) (s_iterno+1)
          else
            begin
              (* COLLECTION OF GARBAGED EQUALITIES *)
              let bag = 
                if max g_iterno s_iterno mod 40 = 0 then
                  (print_status (max g_iterno s_iterno) goals active passive;
                  let active = List.map Equality.id_of (fst active) in
                  let passive = List.map Equality.id_of (fst3 passive) in
                  let goal = ids_of_goal_set goals in
                  Equality.collect bag active passive goal)
                else
                  bag
              in
              if s_iterno > saturation_steps then
                step bag goals passive active (g_iterno+1) (s_iterno+1)
                (* ParamodulationFailure ("max saturation steps",active,passive,bag) *)
              else
                let current, passive = select env goals passive in
                  match add_to_active_aux bag active passive env eq_uri current with
                  | None, active, passive, bag ->
                      step bag goals passive active (g_iterno+1) (s_iterno+1)
                  | Some new', active, passive, bag ->
                      let bag, active_goals, passive_goals = 
                        infer_goal_set_with_current bag env current goals active 
                      in
                      let goals = 
                        let a,b,_ = build_table new' in
                        let rc = 
                          simplify_goal_set bag env (active_goals,passive_goals) (a,b) 
                        in
                        rc
                      in
                      step bag goals passive active (g_iterno+1) (s_iterno+1)
            end
  in
    step bag goals passive active 0 0
;;

let rec saturate_equations bag eq_uri env goal accept_fun passive active =
  elapsed_time := Unix.gettimeofday () -. !start_time;
  if !elapsed_time > !time_limit then
    bag, active, passive
  else
    let current, passive = select env ([goal],[]) passive in
    let bag, res = forward_simplify bag eq_uri env current active in
    match res with
    | None ->
        saturate_equations bag eq_uri env goal accept_fun passive active
    | Some current ->
        Utils.debug_print (lazy (Printf.sprintf "selected: %s"
                             (Equality.string_of_equality ~env current)));
        let bag, new' = infer bag eq_uri env current active in
        let active =
          if Equality.is_identity env current then active
          else
            let al, tbl = active in
            al @ [current], Indexing.index tbl current
        in
        (* alla fine new' contiene anche le attive semplificate!
         * quindi le aggiungo alle passive insieme alle new *)
        let rec simplify bag new' active passive =
          let bag, new' = forward_simplify_new bag eq_uri env new' active in
          let bag, active, newa, pruned =
            backward_simplify bag eq_uri env new' active in
          let passive = 
            List.fold_left (filter_dependent bag) passive pruned in
          match newa with
          | None -> bag, active, passive, new'
          | Some p -> simplify bag (new' @ p) active passive
        in
        let bag, active, passive, new' = simplify bag new' active passive in
        let _ =
          Utils.debug_print
            (lazy
               (Printf.sprintf "active:\n%s\n"
                  (String.concat "\n"
                     (List.map
                         (fun e -> Equality.string_of_equality ~env e)
                         (fst active)))))
        in
        let _ =
          Utils.debug_print
            (lazy
               (Printf.sprintf "new':\n%s\n"
                  (String.concat "\n"
                     (List.map
                         (fun e -> "Negative " ^
                            (Equality.string_of_equality ~env e)) new'))))
        in
        let new' = List.filter accept_fun new' in
        let passive = add_to_passive passive new' [] in
        saturate_equations bag eq_uri env goal accept_fun passive active
;;
  
let default_depth = !maxdepth
and default_width = !maxwidth;;

let reset_refs () =
  symbols_counter := 0;
  weight_age_counter := !weight_age_ratio;
  processed_clauses := 0;
  start_time := 0.;
  elapsed_time := 0.;
  maximal_retained_equality := None;
  infer_time := 0.;
  forward_simpl_time := 0.;
  forward_simpl_new_time := 0.;
  backward_simpl_time := 0.;
  passive_maintainance_time := 0.;
  derived_clauses := 0;
  kept_clauses := 0;
;;

let add_to_active bag active passive env ty term newmetas = 
   reset_refs ();
   match LibraryObjects.eq_URI () with
   | None -> active, passive, bag
   | Some eq_uri -> 
       try 
         let bag, current = Equality.equality_of_term bag term ty newmetas in
         let w,_,_,_,_ = Equality.open_equality current in
         if w > 100 then 
           (HLog.debug 
             ("skipping giant " ^ CicPp.ppterm term ^ " of weight " ^
                string_of_int w); active, passive, bag)
         else
          let bag, current = Equality.fix_metas bag current in
          match add_to_active_aux bag active passive env eq_uri current with
          | _,a,p,b -> a,p,b
       with
       | Equality.TermIsNotAnEquality -> active, passive, bag
;;


let eq_of_goal = function
  | Cic.Appl [Cic.MutInd(uri,0,_);_;_;_] when LibraryObjects.is_eq_URI uri ->
      uri
  | _ -> raise (ProofEngineTypes.Fail (lazy ("The goal is not an equality ")))
;;

let eq_and_ty_of_goal = function
  | Cic.Appl [Cic.MutInd(uri,0,_);t;_;_] when LibraryObjects.is_eq_URI uri ->
      uri,t
  | _ -> raise (ProofEngineTypes.Fail (lazy ("The goal is not an equality ")))
;;

(* fix proof takes in input a term and try to build a metasenv for it *)

let fix_proof metasenv context all_implicits p =
  let rec aux metasenv n p =
    match p with
      | Cic.Meta (i,_) -> 
          if all_implicits then 
	    metasenv,Cic.Implicit None
	  else
	  let irl = 
	    CicMkImplicit.identity_relocation_list_for_metavariable context 
	  in
          let meta = CicSubstitution.lift n (Cic.Meta (i,irl)) in
	  let metasenv =
	    try 
	    let _ = CicUtil.lookup_meta i metasenv in metasenv
	    with CicUtil.Meta_not_found _ ->
            debug_print (lazy ("not found: "^(string_of_int i)));
	    let metasenv,j = CicMkImplicit.mk_implicit_type metasenv [] context in
	      (i,context,Cic.Meta(j,irl))::metasenv
	  in
	    metasenv,meta
      | Cic.Appl l ->
	  let metasenv,l=
            List.fold_right 
	      (fun a (metasenv,l) -> 
		 let metasenv,a' = aux metasenv n a in
		   metasenv,a'::l)
	      l (metasenv,[])
	  in metasenv,Cic.Appl l
      | Cic.Lambda(name,s,t) ->
	  let metasenv,s = aux metasenv n s in
	  let metasenv,t = aux metasenv (n+1) t in
	    metasenv,Cic.Lambda(name,s,t)
      | Cic.Prod(name,s,t) ->
	  let metasenv,s = aux metasenv n s in
	  let metasenv,t = aux metasenv (n+1) t in
	    metasenv,Cic.Prod(name,s,t)
      | Cic.LetIn(name,s,ty,t) ->
	  let metasenv,s = aux metasenv n s in
	  let metasenv,ty = aux metasenv n ty in
	  let metasenv,t = aux metasenv (n+1) t in
	    metasenv,Cic.LetIn(name,s,ty,t)
      | Cic.Const(uri,ens) -> 
	  let metasenv,ens =
	    List.fold_right 
	      (fun (v,a) (metasenv,ens) -> 
		 let metasenv,a' = aux metasenv n a in
		   metasenv,(v,a')::ens)
	      ens (metasenv,[])
	  in
	  metasenv,Cic.Const(uri,ens)
      | t -> metasenv,t
  in
  aux metasenv 0 p 
;;

let fix_metasenv context metasenv =
  List.fold_left 
    (fun m (i,c,t) ->
       let m,t = fix_proof m context false t in
       let m = List.filter (fun (j,_,_) -> j<>i) m in
	 (i,context,t)::m)
    metasenv metasenv
;;


(* status: input proof status
 * goalproof: forward steps on goal
 * newproof: backward steps
 * subsumption_id: the equation used if goal is closed by subsumption
 *   (0 if not closed by subsumption) (DEBUGGING: can be safely removed)
 * subsumption_subst: subst to make newproof and goalproof match
 * proof_menv: final metasenv
 *)

let build_proof 
  bag status  
  goalproof newproof subsumption_id subsumption_subst proof_menv
=
  if proof_menv = [] then debug_print (lazy "+++++++++++++++VUOTA")
  else debug_print (lazy (CicMetaSubst.ppmetasenv [] proof_menv));
  let proof, goalno = status in
  let uri, metasenv, _subst, meta_proof, term_to_prove, attrs = proof in
  let _, context, type_of_goal = CicUtil.lookup_meta goalno metasenv in
  let eq_uri = eq_of_goal type_of_goal in 
  let names = Utils.names_of_context context in
  debug_print (lazy "Proof:");
  debug_print (lazy 
    (Equality.pp_proof bag names goalproof newproof subsumption_subst
       subsumption_id type_of_goal));
(*
      prerr_endline ("max weight: " ^ 
	(string_of_int (Equality.max_weight goalproof newproof)));
*)
  (* generation of the CIC proof *) 
  (* let metasenv' = List.filter (fun i,_,_ -> i<>goalno) metasenv in *)
  let side_effects = 
    List.filter (fun i -> i <> goalno)
      (ProofEngineHelpers.compare_metasenvs 
         ~newmetasenv:metasenv ~oldmetasenv:proof_menv) in
  let goal_proof, side_effects_t = 
    let initial = Equality.add_subst subsumption_subst newproof in
      Equality.build_goal_proof bag
        eq_uri goalproof initial type_of_goal side_effects
        context proof_menv  
  in
(*   Equality.draw_proof bag names goalproof newproof subsumption_id; *)
  let goal_proof = Subst.apply_subst subsumption_subst goal_proof in
  (* assert (metasenv=[]); *)
  let real_menv =  fix_metasenv context (proof_menv@metasenv) in
  let real_menv,goal_proof = 
    fix_proof real_menv context false goal_proof in
(*
  let real_menv,fixed_proof = fix_proof proof_menv context false goal_proof in
    (* prerr_endline ("PROOF: " ^ CicPp.pp goal_proof names); *)
*)
  let pp_error goal_proof names error exn =
    prerr_endline "THE PROOF DOES NOT TYPECHECK! <begin>";
    prerr_endline (CicPp.pp goal_proof names); 
    prerr_endline "THE PROOF DOES NOT TYPECHECK!";
    prerr_endline error;
    prerr_endline "THE PROOF DOES NOT TYPECHECK! <end>";
    raise exn
  in
  let old_insert_coercions = !CicRefine.insert_coercions in
  let goal_proof,goal_ty,real_menv,_ = 
    (* prerr_endline ("parte la refine per: " ^ (CicPp.pp goal_proof names)); *)
    try
            debug_print (lazy (CicPp.ppterm goal_proof));
            CicRefine.insert_coercions := false;
            let res = 
              CicRefine.type_of_aux' 
                real_menv context goal_proof CicUniv.empty_ugraph
            in
            CicRefine.insert_coercions := old_insert_coercions;
            res
    with 
      | CicRefine.RefineFailure s 
      | CicRefine.Uncertain s 
      | CicRefine.AssertFailure s as exn -> 
          CicRefine.insert_coercions := old_insert_coercions;
          pp_error goal_proof names (Lazy.force s) exn
      | CicUtil.Meta_not_found i as exn ->
          CicRefine.insert_coercions := old_insert_coercions;
          pp_error goal_proof names ("META NOT FOUND: "^string_of_int i) exn
      | Invalid_argument "list_fold_left2" as exn ->
          CicRefine.insert_coercions := old_insert_coercions;
          pp_error goal_proof names "Invalid_argument: list_fold_left2" exn 
      | exn ->
          CicRefine.insert_coercions := old_insert_coercions;
          raise exn
  in     
  let subst_side_effects,real_menv,_ = 
    try
      CicUnification.fo_unif_subst [] context real_menv
        goal_ty type_of_goal CicUniv.empty_ugraph
    with
      | CicUnification.UnificationFailure s
      | CicUnification.Uncertain s 
      | CicUnification.AssertFailure s -> assert false
	  (*            fail "Maybe the local context of metas in the goal was not an IRL" s *)
  in
  Utils.debug_print (lazy "+++++++++++++ FINE UNIF");
  let final_subst = 
    (goalno,(context,goal_proof,type_of_goal))::subst_side_effects
  in
(*
      let metas_of_proof = Utils.metas_of_term goal_proof in
*)
  let proof, real_metasenv = 
    ProofEngineHelpers.subst_meta_and_metasenv_in_proof
      proof goalno final_subst
      (List.filter (fun i,_,_ -> i<>goalno ) real_menv)
  in      
  let open_goals = 
    (ProofEngineHelpers.compare_metasenvs 
       ~oldmetasenv:metasenv ~newmetasenv:real_metasenv) in
(*
  let open_goals =
    List.map (fun i,_,_ -> i) real_metasenv in
*)
  final_subst, proof, open_goals


(*

      let metas_still_open_in_proof = Utils.metas_of_term goal_proof in
      (* prerr_endline (CicPp.pp goal_proof names); *)
      let goal_proof = (* Subst.apply_subst subsumption_subst *) goal_proof in
      let side_effects_t = 
        List.map (Subst.apply_subst subsumption_subst) side_effects_t
      in
      (* replacing fake mets with real ones *)
      (* prerr_endline "replacing metas..."; *)
      let irl=CicMkImplicit.identity_relocation_list_for_metavariable context in
      CicMetaSubst.ppmetasenv [] proof_menv;
      let what, with_what = 
        List.fold_left 
          (fun (acc1,acc2) i -> 
	     (Cic.Meta(i,[]))::acc1, (Cic.Implicit None)::acc2)
          ([],[])
	  metas_still_open_in_proof
(*
          (List.filter 
           (fun (i,_,_) -> 
             List.mem i metas_still_open_in_proof
             (*&& not(List.mem i metas_still_open_in_goal)*)) 
           proof_menv)
*)
      in
      let goal_proof_menv =
	List.filter 
          (fun (i,_,_) -> List.mem i metas_still_open_in_proof)
             proof_menv
      in
      let replace where = 
        (* we need this fake equality since the metas of the hypothesis may be
         * with a real local context *)
        ProofEngineReduction.replace_lifting 
          ~equality:(fun x y -> 
            match x,y with Cic.Meta(i,_),Cic.Meta(j,_) -> i=j | _-> false)
          ~what ~with_what ~where
      in
      let goal_proof = replace goal_proof in
        (* ok per le meta libere... ma per quelle che c'erano e sono rimaste? 
         * what mi pare buono, sostituisce solo le meta farlocche *)
      let side_effects_t = List.map replace side_effects_t in
      let free_metas = 
        List.filter (fun i -> i <> goalno)
          (ProofEngineHelpers.compare_metasenvs 
            ~oldmetasenv:metasenv ~newmetasenv:goal_proof_menv)
      in
      (* prerr_endline 
       *   ("freemetas: " ^ 
       *   String.concat "," (List.map string_of_int free_metas) ); *)
      (* check/refine/... build the new proof *)
      let replaced_goal = 
        ProofEngineReduction.replace
          ~what:side_effects ~with_what:side_effects_t
          ~equality:(fun i t -> match t with Cic.Meta(j,_)->j=i|_->false)
          ~where:type_of_goal
      in
      let goal_proof,goal_ty,real_menv,_ = 
        try
          CicRefine.type_of_aux' metasenv context goal_proof
            CicUniv.empty_ugraph
        with 
        | CicUtil.Meta_not_found _ 
        | CicRefine.RefineFailure _ 
        | CicRefine.Uncertain _ 
        | CicRefine.AssertFailure _
        | Invalid_argument "list_fold_left2" as exn ->
            prerr_endline "THE PROOF DOES NOT TYPECHECK!";
            prerr_endline (CicPp.pp goal_proof names); 
            prerr_endline "THE PROOF DOES NOT TYPECHECK!";
            raise exn
      in      
      prerr_endline "+++++++++++++ METASENV";
      prerr_endline
       (CicMetaSubst.ppmetasenv [] real_menv);
      let subst_side_effects,real_menv,_ = 
(* 
        prerr_endline ("XX type_of_goal  " ^ CicPp.ppterm type_of_goal);
        prerr_endline ("XX replaced_goal " ^ CicPp.ppterm replaced_goal);
        prerr_endline ("XX metasenv      " ^ 
        CicMetaSubst.ppmetasenv [] (metasenv @ free_metas_menv));
*)
        try
          CicUnification.fo_unif_subst [] context real_menv
           goal_ty type_of_goal CicUniv.empty_ugraph
        with
        | CicUnification.UnificationFailure s
        | CicUnification.Uncertain s 
        | CicUnification.AssertFailure s -> assert false
(*            fail "Maybe the local context of metas in the goal was not an IRL" s *)
      in
      let final_subst = 
        (goalno,(context,goal_proof,type_of_goal))::subst_side_effects
      in
(*
      let metas_of_proof = Utils.metas_of_term goal_proof in
*)
      let proof, real_metasenv = 
        ProofEngineHelpers.subst_meta_and_metasenv_in_proof
          proof goalno (CicMetaSubst.apply_subst final_subst) 
	  (List.filter (fun i,_,_ -> i<>goalno ) real_menv)
      in
      let open_goals =
	List.map (fun i,_,_ -> i) real_metasenv in

(*
        HExtlib.list_uniq (List.sort Pervasives.compare metas_of_proof) 
      in *)
(*
        match free_meta with Some(Cic.Meta(m,_)) when m<>goalno ->[m] | _ ->[] 
      in
*)
(*
      Printf.eprintf 
        "GOALS APERTI: %s\nMETASENV PRIMA:\n%s\nMETASENV DOPO:\n%s\n" 
          (String.concat ", " (List.map string_of_int open_goals))
          (CicMetaSubst.ppmetasenv [] metasenv)
          (CicMetaSubst.ppmetasenv [] real_metasenv);
*)
      final_subst, proof, open_goals
;;
*)

(* **************** HERE ENDS THE PARAMODULATION STUFF ******************** *)

(* exported functions  *)

let pump_actives context bag active passive saturation_steps max_time =
  reset_refs();
(*
  let max_l l = 
    List.fold_left 
     (fun acc e -> let _,_,_,menv,_ = Equality.open_equality e in
      List.fold_left (fun acc (i,_,_) -> max i acc) acc menv)
     0 l in
*)
(*   let active_l = fst active in *)
(*   let passive_l = fst passive in *)
(*   let ma = max_l active_l in *)
(*   let mp = max_l passive_l in *)
  match LibraryObjects.eq_URI () with
    | None -> active, passive, bag
    | Some eq_uri -> 
	let env = [],context,CicUniv.empty_ugraph in
	  (match 
	     given_clause bag eq_uri env ([],[]) 
	       passive active 0 saturation_steps max_time
	   with
           | ParamodulationFailure (_,a,p,b) -> 
		 a, p, b
	     | ParamodulationSuccess _ ->
		 assert false)
;;

let all_subsumed bag status active passive =
  let proof, goalno = status in
  let uri, metasenv, _subst, meta_proof, term_to_prove, attrs = proof in
  let _, context, type_of_goal = CicUtil.lookup_meta goalno metasenv in
  let env = metasenv,context,CicUniv.empty_ugraph in
  let cleaned_goal = Utils.remove_local_context type_of_goal in
  let canonical_menv,other_menv = 
    List.partition (fun (_,c,_) -> c = context)  metasenv in
  (* prerr_endline ("other menv = " ^ (CicMetaSubst.ppmetasenv [] other_menv));   *)
  let metasenv = List.map (fun (i,_,ty)-> (i,[],ty)) canonical_menv in
  let goal = [], List.filter (fun (i,_,_)->i<>goalno) metasenv, cleaned_goal in
  debug_print (lazy (string_of_int (List.length (fst active))));
   (* we simplify using both actives passives *)
  let table = 
    List.fold_left 
      (fun (l,tbl) eq -> eq::l,(Indexing.index tbl eq))
      active (list_of_passive passive) in
  let (_,_,ty) = goal in
  debug_print (lazy ("prima " ^ CicPp.ppterm ty));
  let _,goal = simplify_goal bag env goal table in
  let (_,_,ty) = goal in
  debug_print (lazy ("in mezzo " ^ CicPp.ppterm ty));
  let bag, subsumed = find_all_subsumed bag env (snd table) goal in
  debug_print (lazy ("dopo " ^ CicPp.ppterm ty));
  let subsumed_or_id =
    match (check_if_goal_is_identity env goal) with
	None -> subsumed
      | Some id -> id::subsumed in
  debug_print (lazy "dopo subsumed");
  let res =
    List.map 
      (fun 
	 (goalproof,newproof,subsumption_id,subsumption_subst, proof_menv) ->
	   let subst, proof, gl =
	     build_proof bag
               status goalproof newproof subsumption_id subsumption_subst proof_menv
	   in
	   let uri, metasenv, subst, meta_proof, term_to_prove, attrs = proof in
           let newmetasenv = 
             other_menv @ 
             List.filter
               (fun x,_,_ -> not (List.exists (fun y,_,_ -> x=y) other_menv)) metasenv
           in
	   let proof = uri, newmetasenv, subst, meta_proof, term_to_prove, attrs in
	     (subst, proof,gl)) subsumed_or_id 
  in 
  res
;;


let given_clause 
  bag status active passive goal_steps saturation_steps max_time 
=
  reset_refs();
  let active_l = fst active in
  let proof, goalno = status in
  let uri, metasenv, _subst, meta_proof, term_to_prove, attrs = proof in
  let _, context, type_of_goal = CicUtil.lookup_meta goalno metasenv in
  let eq_uri = eq_of_goal type_of_goal in 
  let cleaned_goal = Utils.remove_local_context type_of_goal in
  let metas_occurring_in_goal = CicUtil.metas_of_term cleaned_goal in
  let canonical_menv,other_menv = 
    List.partition (fun (_,c,_) -> c = context)  metasenv in
  Utils.set_goal_symbols cleaned_goal; (* DISACTIVATED *)
  let canonical_menv = 
    List.map 
     (fun (i,_,ty)-> (i,[],Utils.remove_local_context ty)) canonical_menv 
  in
  let metasenv' = 
    List.filter 
      (fun (i,_,_)-> i<>goalno && List.mem_assoc i metas_occurring_in_goal) 
      canonical_menv 
  in
  let goal = [], metasenv', cleaned_goal in
  let env = metasenv,context,CicUniv.empty_ugraph in
  debug_print (lazy ">>>>>> ACTIVES >>>>>>>>");
  List.iter (fun e -> debug_print (lazy (Equality.string_of_equality ~env e)))
  active_l;
  debug_print (lazy ">>>>>>>>>>>>>>"); 
  let goals = make_goal_set goal in
  match 
    given_clause bag eq_uri env goals passive active 
      goal_steps saturation_steps max_time
  with
  | ParamodulationFailure (msg,a,p,b) ->
      if Utils.debug then prerr_endline msg;
      None, a, p, b
  | ParamodulationSuccess 
    ((goalproof,newproof,subsumption_id,subsumption_subst, proof_menv),a,p,b) ->
    let subst, proof, gl =
      build_proof b
        status goalproof newproof subsumption_id subsumption_subst proof_menv
    in
    let uri, metasenv, subst, meta_proof, term_to_prove, attrs = proof in
    let proof = uri, other_menv@metasenv, subst, meta_proof, term_to_prove, attrs in
    Some (subst, proof,gl),a,p, b
;;

let solve_narrowing bag status active passive goal_steps =
  let proof, goalno = status in
  let uri, metasenv, _subst, meta_proof, term_to_prove, attrs = proof in
  let _, context, type_of_goal = CicUtil.lookup_meta goalno metasenv in
  let cleaned_goal = Utils.remove_local_context type_of_goal in
  let metas_occurring_in_goal = CicUtil.metas_of_term cleaned_goal in
  let canonical_menv,other_menv = 
    List.partition (fun (_,c,_) -> c = context)  metasenv in
  let canonical_menv = 
    List.map 
     (fun (i,_,ty)-> (i,[],Utils.remove_local_context ty)) canonical_menv 
  in
  let metasenv' = 
    List.filter 
      (fun (i,_,_)-> i<>goalno && List.mem_assoc i metas_occurring_in_goal) 
      canonical_menv 
  in
  let goal = [], metasenv', cleaned_goal in
  let env = metasenv,context,CicUniv.empty_ugraph in
  let goals = 
    let table = List.fold_left Indexing.index (last passive) (fst active) in
    goal :: Indexing.demodulation_all_goal bag env table goal 4
  in
  let rec aux newactives newpassives bag = function
    | [] -> bag, (newactives, newpassives)
    | hd::tl ->
        let selected = hd in
        let (_,m1,t1) = selected in
        let already_in = 
          List.exists (fun (_,_,t) -> Equality.meta_convertibility t t1) 
              newactives
        in
        if already_in then 
             aux newactives newpassives bag tl 
          else
            let bag, newpassives =
              if Utils.metas_of_term t1 = [] then 
                bag, newpassives
              else 
                let bag, new' = 
                   Indexing.superposition_left bag env (snd active) selected
                in
                let new' = 
                  List.map 
                    (fun x -> let b, x = simplify_goal bag env x active in x)
                    new'
                in
                bag, newpassives @ new'
            in
            aux (selected::newactives) newpassives bag tl
  in 
  let rec do_n bag ag pg = function
    | 0 -> None, active, passive, bag
    | n -> 
        let bag, (ag, pg) = aux [] [] bag (ag @ pg) in
        match check_if_goals_set_is_solved bag env active passive (ag,pg) with
        | bag, None -> do_n bag ag pg (n-1)
        | bag, Some (gproof,newproof,subsumption_id,subsumption_subst,pmenv)->
            let subst, proof, gl =
              build_proof bag
                status gproof newproof subsumption_id subsumption_subst pmenv
            in
            let uri,metasenv,subst,meta_proof,term_to_prove,attrs = proof in
            let proof = 
              uri, other_menv@metasenv, subst, meta_proof, term_to_prove, attrs
            in
            Some (subst, proof,gl),active,passive, bag
  in
   do_n bag [] goals goal_steps
;;


let add_to_passive eql passives = 
  add_to_passive passives eql eql
;;



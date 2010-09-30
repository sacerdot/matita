(* Copyright (C) 2004, HELM Team.
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

open Printf
open MetadataTypes 

let debug = false
let debug_print s = if debug then prerr_endline (Lazy.force s)

let critical_value = 7
let just_factor = 1

module UriManagerSet = UriManager.UriSet
module SetSet = Set.Make (UriManagerSet)

type term_signature = (UriManager.uri * UriManager.uri list) option * UriManagerSet.t

type cardinality_condition =
  | Eq of int
  | Gt of int
  | Lt of int

type rating_criterion =
  [ `Hits   (** order by number of hits, most used objects first *)
  ]

let default_tables =
   (library_obj_tbl,library_rel_tbl,library_sort_tbl,library_count_tbl)

let current_tables () = 
  (obj_tbl (),rel_tbl (),sort_tbl (), count_tbl ())

let tbln n = "table" ^ string_of_int n

(*
let add_depth_constr depth_opt cur_tbl where =
  match depth_opt with
  | None -> where
  | Some depth -> (sprintf "%s.h_depth = %d" cur_tbl depth) :: where
*)

let mk_positions positions cur_tbl =
  "(" ^
  String.concat " or "
    (List.map
      (fun pos ->
        let pos_str = MetadataPp.pp_position_tag pos in
        match pos with
        | `InBody
        | `InConclusion
        | `InHypothesis
        | `MainConclusion None
        | `MainHypothesis None ->
            sprintf "%s.h_position = \"%s\"" cur_tbl pos_str
        | `MainConclusion (Some r)
        | `MainHypothesis (Some r) ->
            let depth = MetadataPp.pp_relation r in
            sprintf "(%s.h_position = \"%s\" and %s.h_depth %s)"
              cur_tbl pos_str cur_tbl depth)
      (positions :> MetadataTypes.position list)) ^
  ")"

let explode_card_constr = function
  | Eq card -> "=", card
  | Gt card -> ">", card
  | Lt card -> "<", card

let add_card_constr tbl col where = function
  | None -> where
  | Some constr ->
      let op, card = explode_card_constr constr in
      (* count(_utente).hypothesis = 3 *)
      (sprintf "%s.%s %s %d" tbl col op card :: where)

let add_diff_constr tbl where = function
  | None -> where
  | Some constr ->
      let op, card = explode_card_constr constr in
      (sprintf "%s.hypothesis - %s.conclusion %s %d" tbl tbl op card :: where)
      
let add_all_constr ?(tbl=library_count_tbl) (n,from,where) concl full diff =
  match (concl, full, diff) with
  | None, None, None -> (n,from,where)
  | _ -> 
      let cur_tbl = tbln n in
      let from = (sprintf "%s as %s" tbl cur_tbl) :: from in
      let where = add_card_constr cur_tbl "conclusion" where concl in
      let where = add_card_constr cur_tbl "statement" where full in
      let where = add_diff_constr cur_tbl where diff in
      (n+2,from, 
        (if n > 0 then 
          sprintf "table0.source = %s.source" cur_tbl :: where 
        else
          where))
      

let add_constraint ?(start=0) ?(tables=default_tables) (n,from,where) metadata =
  let obj_tbl,rel_tbl,sort_tbl,count_tbl = tables 
  in
  let cur_tbl = tbln n in
  let start_table = tbln start in
  match metadata with
  | `Obj (uri, positions) ->
      let from = (sprintf "%s as %s" obj_tbl cur_tbl) :: from in
      let where = 
        (sprintf "(%s.h_occurrence = \"%s\")" cur_tbl (UriManager.string_of_uri uri)) ::
        mk_positions positions cur_tbl ::
        (if n=start then []
        else [sprintf "%s.source = %s.source" start_table cur_tbl]) @ 
        where
      in
      ((n+2), from, where)
  | `Rel positions ->
      let from = (sprintf "%s as %s" rel_tbl cur_tbl) :: from in
      let where =
        mk_positions positions cur_tbl ::
        (if n=start then []
        else [sprintf "%s.source = %s.source" start_table cur_tbl]) @ 
        where
      in
      ((n+2), from, where)
  | `Sort (sort, positions) ->
      let sort_str = CicPp.ppsort sort in
      let from = (sprintf "%s as %s" sort_tbl cur_tbl) :: from in
      let where =
        (sprintf "%s.h_sort = \"%s\"" cur_tbl sort_str ) ::
            mk_positions positions cur_tbl ::
        (if n=start then 
          []
        else 
          [sprintf "%s.source = %s.source" start_table cur_tbl ]) @ where
      in
      ((n+2), from, where)

let exec dbtype ~(dbd:HSql.dbd) ?rating (n,from,where) =
  let from = String.concat ", " from in
  let where = String.concat " and " where in
  let query =
    match rating with
    | None -> sprintf "select distinct table0.source from %s where %s" from where
    | Some `Hits ->
        sprintf
          ("select distinct table0.source from %s, hits where %s
            and table0.source = hits.source order by hits.no desc")
          from where 
  in
  (* debug_print (lazy query); *) 
  let result = HSql.exec dbtype dbd query in
  HSql.map result
    ~f:(fun row -> 
     match row.(0) with Some s -> UriManager.uri_of_string s 
     | _ -> assert false)
;;

let at_least dbtype ~(dbd:HSql.dbd) ?concl_card ?full_card ?diff ?rating tables
  (metadata: MetadataTypes.constr list)
=
  let obj_tbl,rel_tbl,sort_tbl, count_tbl = tables in
  if (metadata = []) && concl_card = None && full_card = None then
    begin
      HLog.warn "MetadataConstraints.at_least: no constraints given";
      []
    end
  else
    let (n,from,where) =
      List.fold_left (add_constraint ~tables) (0,[],[]) metadata
    in
    let (n,from,where) =
      add_all_constr ~tbl:count_tbl (n,from,where) concl_card full_card diff
    in
    exec dbtype ~dbd ?rating (n,from,where)
;;
    
let at_least  
  ~(dbd:HSql.dbd) ?concl_card ?full_card ?diff ?rating
      (metadata: MetadataTypes.constr list)
=
  if are_tables_ownerized () then
    at_least 
      HSql.Library ~dbd ?concl_card ?full_card ?diff ?rating 
        default_tables metadata
    @
    at_least 
      HSql.Legacy ~dbd ?concl_card ?full_card ?diff ?rating 
        default_tables metadata
    @
    at_least 
      HSql.User ~dbd ?concl_card ?full_card ?diff ?rating 
        (current_tables ()) metadata

  else
    at_least 
      HSql.Library ~dbd ?concl_card ?full_card ?diff ?rating 
        default_tables metadata 
    @
    at_least 
      HSql.Legacy ~dbd ?concl_card ?full_card ?diff ?rating 
        default_tables metadata 
  
    
  (** Prefix handling *)

let filter_by_card n =
  SetSet.filter (fun t -> (UriManagerSet.cardinal t) <= n)
  
let merge n a b = 
  let init = SetSet.union a b in
  let merge_single_set s1 b = 
    SetSet.fold 
      (fun s2 res -> SetSet.add (UriManagerSet.union s1 s2) res)
      b SetSet.empty in
  let res = 
    SetSet.fold (fun s1 res -> SetSet.union (merge_single_set s1 b) res) a init
  in
  filter_by_card n res 

let rec inspect_children n childs =
  List.fold_left 
    (fun res term -> merge n (inspect_conclusion n term) res)
    SetSet.empty childs 

and add_root n root childs =
  let childunion = inspect_children n childs in
  let addroot = UriManagerSet.add root in
    SetSet.fold 
      (fun child newsets -> SetSet.add (addroot child) newsets)
      childunion 
      (SetSet.singleton (UriManagerSet.singleton root))

and inspect_conclusion n t = 
  if n = 0 then SetSet.empty
  else match t with
      Cic.Rel _                    
    | Cic.Meta _                     
    | Cic.Sort _ 
    | Cic.Implicit _ -> SetSet.empty 
    | Cic.Var (u,exp_named_subst) -> SetSet.empty
    | Cic.Const (u,exp_named_subst) -> 
        SetSet.singleton (UriManagerSet.singleton u)
    | Cic.MutInd (u, t, exp_named_subst) -> 
	SetSet.singleton (UriManagerSet.singleton
          (UriManager.uri_of_uriref u t None))
    | Cic.MutConstruct (u, t, c, exp_named_subst) -> 
	SetSet.singleton (UriManagerSet.singleton
          (UriManager.uri_of_uriref u t (Some c)))
    | Cic.Cast (t, _) -> inspect_conclusion n t
    | Cic.Prod (_, s, t) -> 
	merge n (inspect_conclusion n s) (inspect_conclusion n t)
    | Cic.Lambda (_, s, t) ->
	merge n (inspect_conclusion n s) (inspect_conclusion n t)
    | Cic.LetIn (_, s, ty, t) ->
       merge n (inspect_conclusion n s)
	(merge n (inspect_conclusion n ty) (inspect_conclusion n t))
    | Cic.Appl ((Cic.Const (u,exp_named_subst))::l) ->
	add_root (n-1) u l
    | Cic.Appl ((Cic.MutInd (u, t, exp_named_subst))::l) ->
        let uri = UriManager.uri_of_uriref u t None in
	add_root (n-1) uri l
    | Cic.Appl ((Cic.MutConstruct (u, t, c, exp_named_subst))::l)  ->
	let suri = UriManager.uri_of_uriref u t (Some c) in
	add_root (n-1) suri l
    | Cic.Appl l -> 
	SetSet.empty
    | Cic.MutCase (u, t, tt, uu, m) ->
	SetSet.empty
    | Cic.Fix (_, m) -> 
	SetSet.empty
    | Cic.CoFix (_, m) -> 
	SetSet.empty

let rec inspect_term n t = 
  if n = 0 then
    assert false
  else
    match t with
      Cic.Rel _                    
    | Cic.Meta _                     
    | Cic.Sort _ 
    | Cic.Implicit _ -> None, SetSet.empty 
    | Cic.Var (u,exp_named_subst) -> None, SetSet.empty
    | Cic.Const (u,exp_named_subst) -> 
        Some u, SetSet.empty
    | Cic.MutInd (u, t, exp_named_subst) -> 
        let uri = UriManager.uri_of_uriref u t None in
	Some uri, SetSet.empty
    | Cic.MutConstruct (u, t, c, exp_named_subst) -> 
        let uri = UriManager.uri_of_uriref u t (Some c) in
	Some uri, SetSet.empty
    | Cic.Cast (t, _) -> inspect_term n t
    | Cic.Prod (_, _, t) -> inspect_term n t
    | Cic.LetIn (_, _, _, t) -> inspect_term n t
    | Cic.Appl ((Cic.Const (u,exp_named_subst))::l) ->
	let childunion = inspect_children (n-1) l in
	Some u, childunion
    | Cic.Appl ((Cic.MutInd (u, t, exp_named_subst))::l) ->
	let suri = UriManager.uri_of_uriref u t None in
	if u = HelmLibraryObjects.Logic.eq_URI && n>1 then
	  (* equality is handled in a special way: in particular, 
             the type, if defined, is always added to the prefix, 
	     and n is not decremented - it should have been n-2 *)
	  match l with
	      Cic.Const (u1,exp_named_subst1)::l1 ->
		let inconcl = add_root (n-1) u1 l1 in
		Some suri, inconcl
	    | Cic.MutInd (u1, t1, exp_named_subst1)::l1 ->
		let suri1 = UriManager.uri_of_uriref u1 t1 None in
		let inconcl = add_root (n-1) suri1 l1 in  
		Some suri, inconcl
	    | Cic.MutConstruct (u1, t1, c1, exp_named_subst1)::l1 ->
                let suri1 = UriManager.uri_of_uriref u1 t1 (Some c1) in
		let inconcl = add_root (n-1) suri1 l1 in  
		Some suri, inconcl
	    | _ :: _ -> Some suri, SetSet.empty
	    | _ -> assert false (* args number must be > 0 *)
	else
	  let childunion = inspect_children (n-1) l in
	  Some suri, childunion
    | Cic.Appl ((Cic.MutConstruct (u, t, c, exp_named_subst))::l)  ->
	let suri = UriManager.uri_of_uriref u t(Some c) in
	let childunion = inspect_children (n-1) l in
	Some suri, childunion
    | _ -> None, SetSet.empty

let add_cardinality s =
  let l = SetSet.elements s in
  let res = 
    List.map 
      (fun set -> 
	 let el = UriManagerSet.elements set in
	 (List.length el, el)) l in
    (* ordered by descending cardinality *)
    List.sort (fun (n,_) (m,_) -> m - n) ((0,[])::res)

let prefixes n t =
  match inspect_term n t with
      Some a, set -> Some a, add_cardinality set
    | None, set when (SetSet.is_empty set) -> None, []
    | _, _ -> assert false


let rec add children =
  List.fold_left
    (fun acc t -> UriManagerSet.union (signature_concl t) acc)
    (UriManagerSet.empty) children
  
(* this function creates the set of all different constants appearing in 
   the conclusion of the term *)
and signature_concl = 
  function
      Cic.Rel _                    
    | Cic.Meta _                     
    | Cic.Sort _ 
    | Cic.Implicit _ -> UriManagerSet.empty 
    | Cic.Var (u,exp_named_subst) ->
       (*CSC: TODO if the var has a body it must be processed *)
       UriManagerSet.empty
    | Cic.Const (u,exp_named_subst) -> 
        UriManagerSet.singleton u
    | Cic.MutInd (u, t, exp_named_subst) -> 
        let rec projections_of uris =
          List.flatten
           (List.map 
            (fun uri ->
              let o,_ = CicEnvironment.get_obj CicUniv.oblivion_ugraph uri in
              projections_of (CicUtil.projections_of_record o uri))
            uris)
        in
        let uri = UriManager.uri_of_uriref u t None in
        List.fold_right UriManagerSet.add
          (projections_of [u]) (UriManagerSet.singleton uri)
    | Cic.MutConstruct (u, t, c, exp_named_subst) -> 
        let uri = UriManager.uri_of_uriref u t (Some c) in
        UriManagerSet.singleton uri
    | Cic.Cast (t, _) -> signature_concl t
    | Cic.Prod (_, s, t) -> 
	UriManagerSet.union (signature_concl s) (signature_concl t)
    | Cic.Lambda (_, s, t) ->
	UriManagerSet.union (signature_concl s) (signature_concl t)
    | Cic.LetIn (_, s, ty, t) ->
       UriManagerSet.union (signature_concl s)
	(UriManagerSet.union (signature_concl ty) (signature_concl t))
    | Cic.Appl l  -> add l
    | Cic.MutCase _
    | Cic.Fix _
    | Cic.CoFix _ ->
	UriManagerSet.empty

let rec signature_of = function
  | Cic.Cast (t, _)      -> signature_of t
  | Cic.Prod (_, _, t)   -> signature_of t               
  | Cic.LetIn (_, _, _, t) -> signature_of t
  | Cic.Appl ((Cic.Const (u,exp_named_subst))::l) ->
      Some (u, []), add l
  | Cic.Appl ((Cic.MutInd (u, t, exp_named_subst))::l) ->
      let suri = UriManager.uri_of_uriref u t None in
       if LibraryObjects.is_eq_URI u then 
	  (* equality is handled in a special way: in particular, 
             the type, if defined, is always added to the prefix, 
	     and n is not decremented - it should have been n-2 *)
      match l with
	  Cic.Const (u1,exp_named_subst1)::l1 ->
	    let inconcl = UriManagerSet.remove u1 (add l1) in
            Some (suri, [u1]), inconcl
	| Cic.MutInd (u1, t1, exp_named_subst1)::l1 ->
	    let suri1 = UriManager.uri_of_uriref u1 t1 None in
	    let inconcl =  UriManagerSet.remove suri1 (add l1) in
	      Some (suri, [suri1]), inconcl
	| Cic.MutConstruct (u1, t1, c1, exp_named_subst1)::l1 ->
            let suri1 = UriManager.uri_of_uriref u1 t1 (Some c1) in
	    let inconcl =  UriManagerSet.remove suri1 (add l1) in
            Some (suri, [suri1]), inconcl
	| _ :: tl -> Some (suri, []), add tl
	| _ -> assert false (* args number must be > 0 *)
      else
	Some (suri, []), add l
  | Cic.Appl ((Cic.MutConstruct (u, t, c, exp_named_subst))::l)  ->
      let suri = UriManager.uri_of_uriref u t (Some c) in
      Some (suri, []), add l
  | t -> None, signature_concl t

(* takes a list of lists and returns the list of all elements
   without repetitions *)
let union l = 
  let rec drop_repetitions = function
      [] -> []
    | [a] -> [a]
    | u1::u2::l when u1 = u2 -> drop_repetitions (u2::l)
    | u::l -> u::(drop_repetitions l) in
  drop_repetitions (List.sort Pervasives.compare (List.concat l))

let must_of_prefix ?(where = `Conclusion) m s =
  let positions =
    match where with
    | `Conclusion -> [`InConclusion]
    | `Statement -> [`InConclusion; `InHypothesis; `MainHypothesis None]
  in
  let positions =
   if m = None then `MainConclusion None :: positions else positions in
  let s' = List.map (fun (u:UriManager.uri) -> `Obj (u, positions)) s in
   match m with
      None -> s'
    | Some m -> `Obj (m, [`MainConclusion None]) :: s'

let escape = Str.global_replace (Str.regexp_string "\'") "\\'"

let get_constants (dbd:HSql.dbd) ~where uri =
  let uri = escape (UriManager.string_of_uri uri) in
  let positions =
    match where with
    | `Conclusion -> [ MetadataTypes.mainconcl_pos; MetadataTypes.inconcl_pos ]
    | `Statement ->
        [ MetadataTypes.mainconcl_pos; MetadataTypes.inconcl_pos;
          MetadataTypes.inhyp_pos; MetadataTypes.mainhyp_pos ]
  in
  let pos_predicate =
    String.concat " OR "
      (List.map (fun pos -> sprintf "(h_position = \"%s\")" pos) positions)
  in
  let query tbl = 
    sprintf "SELECT h_occurrence FROM %s WHERE source=\"%s\" AND (%s)"
      tbl uri pos_predicate
  in
  let db = [
    HSql.Library, MetadataTypes.library_obj_tbl;
    HSql.Legacy, MetadataTypes.library_obj_tbl;
    HSql.User, MetadataTypes.obj_tbl ()]
  in
  let set = ref UriManagerSet.empty in
  List.iter
    (fun (dbtype, table) ->
      let result = HSql.exec dbtype dbd (query table) in
      HSql.iter result
        (fun col ->
         match col.(0) with
         | Some uri -> 
             set := UriManagerSet.add (UriManager.uri_of_string uri) !set
         | _ -> assert false)) 
    db;
  !set

let at_most ~(dbd:HSql.dbd) ?(where = `Conclusion) only u =
  let inconcl = get_constants dbd ~where u in
  UriManagerSet.subset inconcl only

  (* Special handling of equality. The problem is filtering out theorems just
  * containing variables (e.g. all the theorems in cic:/Coq/Ring/). Really
  * ad-hoc, no better solution found at the moment *)
let myspeciallist_of_facts  =
  [0,UriManager.uri_of_string "cic:/Coq/Init/Logic/eq.ind#xpointer(1/1/1)"]
let myspeciallist =
  [0,UriManager.uri_of_string "cic:/Coq/Init/Logic/eq.ind#xpointer(1/1/1)";
   (* 0,"cic:/Coq/Init/Logic/sym_eq.con"; *)
   0,UriManager.uri_of_string "cic:/Coq/Init/Logic/trans_eq.con";
   0,UriManager.uri_of_string "cic:/Coq/Init/Logic/f_equal.con";
   0,UriManager.uri_of_string "cic:/Coq/Init/Logic/f_equal2.con";
   0,UriManager.uri_of_string "cic:/Coq/Init/Logic/f_equal3.con"]


let compute_exactly ~(dbd:HSql.dbd) ?(facts=false) ~where main prefixes =
  List.concat
    (List.map 
      (fun (m,s) -> 
        let is_eq,card =
         match main with
            None -> false,m
          | Some main ->
             (m = 0 &&
              UriManager.eq main
               (UriManager.uri_of_string (HelmLibraryObjects.Logic.eq_XURI))),
             m+1
        in
        if m = 0 && is_eq then
          (if facts then myspeciallist_of_facts
	   else myspeciallist)
        else
          let res =
           (* this gets rid of the ~750 objects of type Set/Prop/Type *)
           if card = 0 then []
           else
            let must = must_of_prefix ~where main s in
            match where with
            | `Conclusion -> at_least ~dbd ~concl_card:(Eq card) must
            | `Statement -> at_least ~dbd ~full_card:(Eq card) must
          in
          List.map (fun uri -> (card, uri)) res)
      prefixes)

  (* critical value reached, fallback to "only" constraints *)

let compute_with_only ~(dbd:HSql.dbd) ?(facts=false) ?(where = `Conclusion) 
  main prefixes constants
=
  let max_prefix_length = 
    match prefixes with
    | [] -> assert false 
    | (max,_)::_ -> max in
  let maximal_prefixes = 
    let rec filter res = function 
        [] -> res
      | (n,s)::l when n = max_prefix_length -> filter ((n,s)::res) l
      | _::_-> res in
    filter [] prefixes in
    let greater_than =
    let all =
      union
        (List.map 
          (fun (m,s) -> 
            let card = if main = None then m else m + 1 in
            let must = must_of_prefix ~where main s in
            (let res = 
              match where with
              | `Conclusion -> at_least ~dbd ~concl_card:(Gt card) must
              | `Statement -> at_least ~dbd ~full_card:(Gt card) must
            in
            (* we tag the uri with m+1, for sorting purposes *)
            List.map (fun uri -> (card, uri)) res))
          maximal_prefixes)
    in
(*     Printf.fprintf stderr "all: %d\n" (List.length all);flush_all (); *)
(*
    List.filter (function (_,uri) -> 
      at_most ~dbd ~where constants uri) 
*)
    all 
    in
  let equal_to = compute_exactly ~dbd ~facts ~where main prefixes in
    greater_than @ equal_to

  (* real match query implementation *)

let cmatch ~(dbd:HSql.dbd)  ?(facts=false) t =
  let (main, constants) = signature_of t in
  match main with
  | None -> []
  | Some (main, types) ->
      (* the type of eq is not counted in constants_no *)
      let types_no = List.length types in
      let constants_no = UriManagerSet.cardinal constants in
      if (constants_no > critical_value) then 
        let prefixes = prefixes just_factor t in
        (match prefixes with
        | Some main, all_concl ->
            let all_constants = 
              List.fold_right UriManagerSet.add types (UriManagerSet.add main constants)
            in
            compute_with_only ~dbd ~facts (Some main) all_concl all_constants
         | _, _ -> [])
      else
        (* in this case we compute all prefixes, and we do not need
           to apply the only constraints *)
        let prefixes =
          if constants_no = 0 then
	    (if types_no = 0 then
	       Some main, [0, []]
	     else
	       Some main, [0, []; types_no, types])
          else
            prefixes (constants_no+types_no+1) t
        in
        (match prefixes with
           Some main, all_concl ->
	    compute_exactly ~dbd ~facts ~where:`Conclusion (Some main) all_concl
         | _, _ -> [])

let power_upto upto consts =
  let l = UriManagerSet.elements consts in
  List.sort (fun (n,_) (m,_) -> m - n)
  (List.fold_left 
    (fun res a ->
       let res' = 
	 List.filter (function (n,l) -> n <= upto)
	   (List.map (function (n,l) -> (n+1,a::l)) res) in
	 res@res')
     [(0,[])] l)

let power consts =
  let l = UriManagerSet.elements consts in
  List.sort (fun (n,_) (m,_) -> m - n)
  (List.fold_left 
    (fun res a -> res@(List.map (function (n,l) -> (n+1,a::l)) res)) 
     [(0,[])] l)

type where = [ `Conclusion | `Statement ]

let sigmatch ~(dbd:HSql.dbd) ?(facts=false) ?(where = `Conclusion)
 (main, constants)
=
 let main,types =
   match main with
     None -> None,[]
   | Some (main, types) -> Some main,types
 in
  let constants_no = UriManagerSet.cardinal constants in
  (* debug_print (lazy (("constants_no: ")^(string_of_int constants_no))); *)
  if (constants_no > critical_value) then 
    let subsets = 
      let subsets = power_upto just_factor constants in
      (* let _ = debug_print (lazy (("subsets: ")^
	 (string_of_int (List.length subsets)))) in *)
      let types_no = List.length types in 
	if types_no > 0 then  
          List.map (function (n,l) -> (n+types_no,types@l)) subsets
	else subsets
    in
    debug_print (lazy ("critical_value exceded..." ^ string_of_int constants_no));
    let all_constants = 
     let all = match main with None -> types | Some m -> m::types in
      List.fold_right UriManagerSet.add all constants
    in
     compute_with_only ~dbd ~where main subsets all_constants
  else
    (debug_print (lazy ("all subsets..." ^ string_of_int constants_no));
    let subsets = 
      let subsets = power constants in
      let types_no = List.length types in
       if types_no > 0 then  
        (0,[]) :: List.map (function (n,l) -> (n+types_no,types@l)) subsets
       else subsets
    in
       debug_print (lazy "fine1");
       compute_exactly ~dbd ~facts ~where main subsets)

  (* match query wrappers *)

let cmatch'= cmatch 

let cmatch ~dbd ?(facts=false) term =
  List.map snd
    (List.sort
      (fun x y -> Pervasives.compare (fst y) (fst x))
      (cmatch' ~dbd ~facts term))

let constants_of = signature_concl


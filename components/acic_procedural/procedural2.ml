(* Copyright (C) 2003-2005, HELM Team.
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

module C    = Cic
module I    = CicInspect
module S    = CicSubstitution
module R    = CicReduction
module TC   = CicTypeChecker 
module Un   = CicUniv
module UM   = UriManager
module Obj  = LibraryObjects
module A    = Cic2acic
module Ut   = CicUtil
module E    = CicEnvironment
module Pp   = CicPp
module PEH  = ProofEngineHelpers
module HEL  = HExtlib
module DTI  = DoubleTypeInference
module NU   = CicNotationUtil
module L    = Librarian
module G    = GrafiteAst

module Cl   = ProceduralClassify
module T    = ProceduralTypes
module Cn   = ProceduralConversion
module H    = ProceduralHelpers

type status = {
   sorts    : (C.id, A.sort_kind) Hashtbl.t;
   types    : (C.id, A.anntypes) Hashtbl.t;
   params   : G.inline_param list;
   max_depth: int option;
   depth    : int;
   defaults : bool;
   cr       : bool;
   context  : C.context;
   case     : int list
}

let debug = ref false

(* helpers ******************************************************************)

let split2_last l1 l2 =
try
   let n = pred (List.length l1) in
   let before1, after1 = HEL.split_nth n l1 in
   let before2, after2 = HEL.split_nth n l2 in
   before1, before2, List.hd after1, List.hd after2
with Invalid_argument _ -> failwith "A2P.split2_last"
   
let string_of_head = function
   | C.ASort _         -> "sort"
   | C.AConst _        -> "const"
   | C.AMutInd _       -> "mutind"
   | C.AMutConstruct _ -> "mutconstruct"
   | C.AVar _          -> "var"
   | C.ARel _          -> "rel"
   | C.AProd _         -> "prod"
   | C.ALambda _       -> "lambda"
   | C.ALetIn _        -> "letin"
   | C.AFix _          -> "fix"
   | C.ACoFix _        -> "cofix"
   | C.AAppl _         -> "appl"
   | C.ACast _         -> "cast"
   | C.AMutCase _      -> "mutcase"
   | C.AMeta _         -> "meta"
   | C.AImplicit _     -> "implict"

let next st = {st with depth = succ st.depth}

let add st entry = {st with context = entry :: st.context}

let push st = {st with case = 1 :: st.case}

let inc st =
   {st with case = match st.case with 
      | []       -> []
      | hd :: tl -> succ hd :: tl
   }

let case st str =
   let case = String.concat "." (List.rev_map string_of_int st.case) in
   Printf.sprintf "case %s: %s" case str

let test_depth st =
try   
   let msg = Printf.sprintf "Depth %u: " st.depth in
   match st.max_depth with
      | None   -> true, "" 
      | Some d -> if st.depth < d then true, msg else false, "DEPTH EXCEDED: "
with Invalid_argument _ -> failwith "A2P.test_depth"

let is_rewrite_right st = function
   | C.AConst (_, uri, []) -> st.defaults && Obj.is_eq_ind_r_URI uri
   | _                     -> false

let is_rewrite_left st = function
   | C.AConst (_, uri, []) -> st.defaults && Obj.is_eq_ind_URI uri
   | _                     -> false

let is_fwd_rewrite_right st hd tl =
   if is_rewrite_right st hd then match List.nth tl 3 with
      | C.ARel _ -> true
      | _        -> false
   else false

let is_fwd_rewrite_left st hd tl =
   if is_rewrite_left st hd then match List.nth tl 3 with
      | C.ARel _ -> true
      | _        -> false
   else false

let get_inner_types st v =
try
   let id = Ut.id_of_annterm v in
   try match Hashtbl.find st.types id with
      | {A.annsynthesized = ity; A.annexpected = Some ety} -> Some (ity, ety)
      | {A.annsynthesized = ity; A.annexpected = None}     -> Some (ity, ity)
   with Not_found -> None
with Invalid_argument _ -> failwith "P2.get_inner_types"

let get_entry st id =
   let rec aux = function
      | []                                        -> assert false
      | Some (C.Name name, e) :: _ when name = id -> e
      | _ :: tl                                   -> aux tl
   in
   aux st.context

let string_of_atomic = function
   | C.ARel (_, _, _, s)               -> s
   | C.AVar (_, uri, _)                -> H.name_of_uri uri None None
   | C.AConst (_, uri, _)              -> H.name_of_uri uri None None
   | C.AMutInd (_, uri, i, _)          -> H.name_of_uri uri (Some i) None
   | C.AMutConstruct (_, uri, i, j, _) -> H.name_of_uri uri (Some i) (Some j)
   | _                                 -> ""

let get_sub_names head l =
   let s = string_of_atomic head in
   if s = "" then [] else
   let map (names, i) _ = 
      let name = Printf.sprintf "%s_%u" s i in name :: names, succ i
   in
   let names, _ = List.fold_left map ([], 1) l in 
   List.rev names

let get_type msg st t = H.get_type msg st.context (H.cic t) 

let get_uri_of_head = function
   | C.AConst (_, u, _)                                 ->
      Some (u, 0, 0, 0)
   | C.AAppl (_, C.AConst (_, u, _) :: vs)              ->
      Some (u, 0, 0, List.length vs)
   | C.AMutInd (_, u, i, _)                             ->
      Some (u, succ i, 0, 0)
   | C.AAppl (_, C.AMutInd (_, u, i, _) :: vs)          ->
      Some (u, succ i, 0, List.length vs)
   | C.AMutConstruct (_, u, i, j, _)                    ->
      Some (u, succ i, j, 0)
   | C.AAppl (_, C.AMutConstruct (_, u, i, j, _) :: vs) ->
      Some (u, succ i, j, List.length vs)
   | _                                                  ->
      None

let get_uri_of_apply = function
   | T.Exact (t, _)
   | T.Apply (t, _) -> get_uri_of_head t
   | _              -> None

let is_reflexivity st step =
   match get_uri_of_apply step with
      | None                -> false
      | Some (uri, i, j, n) ->
         st.defaults && Obj.is_eq_URI uri && i = 1 && j = 1 && n = 0

let is_ho_reflexivity st step =
   match get_uri_of_apply step with
      | None                -> false
      | Some (uri, i, j, n) ->
         st.defaults && Obj.is_eq_URI uri && i = 1 && j = 1 && n > 0

let are_convertible st pred sx dx =
   let pred, sx, dx = H.cic pred, H.cic sx, H.cic dx in
   let sx, dx = C.Appl [pred; sx], C.Appl [pred; dx] in
   fst (R.are_convertible st.context sx dx Un.default_ugraph)

(* proof construction *******************************************************)

let anonymous_premise = C.Name "UNNAMED"

let mk_lapply_args hd tl classes = 
   let map _ = Cn.meta "" in
   let args = List.rev_map map tl in
   if args = [] then hd else C.AAppl ("", hd :: args)

let mk_apply_args hd tl classes synth qs =
   let exp = ref 0 in
   let map v (cl, b) =
      if I.overlaps synth cl
         then if b then v, v else Cn.meta "", v
         else Cn.meta "", Cn.meta ""
   in
   let rec rev a = function
      | []       -> a
      | hd :: tl -> 
         if snd hd <> Cn.meta "" then incr exp;
         rev (snd hd :: a) tl 
   in
   let rec aux = function
      | []       -> []
      | hd :: tl -> 
         if fst hd = Cn.meta "" then aux tl else rev [] (hd :: tl)
   in
   let args = T.list_rev_map2 map tl classes in
   let args = aux args in
   let part = !exp < List.length tl in
   if args = [] then part, hd, qs else part, C.AAppl ("", hd :: args), qs

let mk_convert st ?name sty ety note =
   let ppterm t = 
      let a = ref "" in Ut.pp_term (fun s -> a := !a ^ s) [] st.context t; !a
   in 
   let e = Cn.hole "" in
   let csty, cety = H.cic sty, H.cic ety in
   let note = 
      if !debug then
         let sname = match name with None -> "" | Some (id, _) -> id in
         Printf.sprintf "%s: %s\nSINTH: %s\nEXP: %s"
            note sname (ppterm csty) (ppterm cety)
      else ""
   in
   if H.alpha ~flatten:true st.context csty cety then [T.Note note] else 
   let sty, ety = H.acic_bc st.context sty, H.acic_bc st.context ety in
   match name with
      | None         -> [T.Change (sty, ety, None, e, note)]
      | Some (id, i) -> 
         begin match get_entry st id with
	    | C.Def _  -> 
	       [T.Change (ety, sty, Some (id, Some id), e, note);
	        T.ClearBody (id, "")
	       ]
	    | C.Decl _ -> 
	       [T.Change (ety, sty, Some (id, Some id), e, note)] 
         end

let convert st ?name v = 
   match get_inner_types st v with
      | None            -> 
         if !debug then [T.Note "NORMAL: NO INNER TYPES"] else []
      | Some (sty, ety) -> mk_convert st ?name sty ety "NORMAL"
	  
let get_intro = function 
   | C.Anonymous -> None
   | C.Name s    -> Some s

let mk_preamble st what script = match script with
   | step :: script when is_reflexivity st step ->
      T.Reflexivity (T.note_of_step step) :: script
   | step :: script when is_ho_reflexivity st step ->
      convert st what @ T.Reflexivity (T.note_of_step step) :: script
   | T.Exact _ :: _ -> script
   | _              -> convert st what @ script   

let mk_arg st = function
   | C.ARel (_, _, i, name) as what -> convert st ~name:(name, i) what
   | _                              -> []

let mk_fwd_rewrite st dtext name tl direction v t ity ety =
   let compare premise = function
      | None   -> true
      | Some s -> s = premise
   in
   assert (List.length tl = 6);
   let what, where, predicate = List.nth tl 5, List.nth tl 3, List.nth tl 2 in
   let e = Cn.mk_pattern 1 ety predicate in
   if (Cn.does_not_occur e) then st, [] else 
   match where with
      | C.ARel (_, _, i, premise) as w ->
         let script name =
            let where = Some (premise, name) in
	    let script = mk_arg st what @ mk_arg st w in
	    T.Rewrite (direction, what, where, e, dtext) :: script
	 in
	 if DTI.does_not_occur (succ i) (H.cic t) || compare premise name then
	    {st with context = Cn.clear st.context premise}, script name
	 else begin
	    assert (Ut.is_sober st.context (H.cic ity));
	    let ity = H.acic_bc st.context ity in
	    let br1 = [T.Id ""] in
	    let br2 = List.rev (T.Exact (w, "assumption") :: script None) in
	    let text = "non-linear rewrite" in
	    st, [T.Branch ([br2; br1], ""); T.Cut (name, ity, text)]
	 end
      | _                         -> assert false

let mk_rewrite st dtext where qs tl direction t ity = 
   let ppterm t = 
      let a = ref "" in Ut.pp_term (fun s -> a := !a ^ s) [] st.context t; !a
   in 
   assert (List.length tl = 5);
   let pred, sx, dx = List.nth tl 2, List.nth tl 1, List.nth tl 4 in
   let dtext = if !debug then dtext ^ ppterm (H.cic pred) else dtext in
   let e = Cn.mk_pattern 1 ity pred in
   let script = [T.Branch (qs, "")] in
   if Cn.does_not_occur e then script else
   if st.cr && are_convertible st pred sx dx then 
      let dtext = "convertible rewrite" ^ dtext in
      let ity, ety, e = Cn.beta sx pred, Cn.beta dx pred, Cn.hole "" in
      let city, cety = H.cic ity, H.cic ety in
      if H.alpha ~flatten:true st.context city cety then script else
      T.Change (ity, ety, None, e, dtext) :: script
   else
   T.Rewrite (direction, where, None, e, dtext) :: script

let rec proc_lambda st what name v t =
   let dtext = if !debug then CicPp.ppcontext st.context else "" in
   let name = match name with
      | C.Anonymous -> H.mk_fresh_name true st.context anonymous_premise
      | name        -> name
   in
   let entry = Some (name, C.Decl (H.cic v)) in
   let intro = get_intro name in
   let script = proc_proof (add st entry) t in
   let script = T.Intros (Some 1, [intro], dtext) :: script in
   mk_preamble st what script

and proc_letin st what name v w t =
   let intro = get_intro name in
   let proceed, dtext = test_depth st in
   let script = if proceed then 
      let st, hyp, rqv = match get_inner_types st what, get_inner_types st v with
         | Some (C.ALetIn (_, _, iv, iw, _), _), _ when
	    H.alpha ~flatten:true st.context (H.cic v) (H.cic iv) &&
	    H.alpha ~flatten:true st.context (H.cic w) (H.cic iw)
	                                           ->
	    st, C.Def (H.cic v, H.cic w), [T.Intros (Some 1, [intro], dtext)]
	 | _, Some (ity, ety)                      ->
	    let st, rqv = match v with
               | C.AAppl (_, hd :: tl) when is_fwd_rewrite_right st hd tl ->
	          mk_fwd_rewrite st dtext intro tl true v t ity ety
	       | C.AAppl (_, hd :: tl) when is_fwd_rewrite_left st hd tl  ->
	          mk_fwd_rewrite st dtext intro tl false v t ity ety
	       | C.AAppl (_, hd :: tl)                                    ->
                  let ty = match get_inner_types st hd with
                     | Some (ity, _) -> H.cic ity 
	             | None          -> get_type "TC3" st hd 
                  in
		  let classes, _ = Cl.classify st.context ty in
                  let parsno, argsno = List.length classes, List.length tl in
                  let decurry = parsno - argsno in
	          if decurry <> 0 then begin		  
(* FG: we fall back in the cut case *)	             
		     assert (Ut.is_sober st.context (H.cic ety));
		     let ety = H.acic_bc st.context ety in
	             let qs = [proc_proof (next st) v; [T.Id ""]] in
		     st, [T.Branch (qs, ""); T.Cut (intro, ety, dtext)]
		  end else
		  let names, synth = get_sub_names hd tl, I.S.empty in
		  let qs = proc_bkd_proofs (next st) synth names classes tl in
                  let hd = mk_lapply_args hd tl classes in
		  let qs = [T.Id ""] :: qs in
		  st, [T.Branch (qs, ""); T.LApply (intro, hd, dtext)]
	       | v                                                        ->
	          assert (Ut.is_sober st.context (H.cic ety));
		  let ety = H.acic_bc st.context ety in
	          let qs = [proc_proof (next st) v; [T.Id ""]] in
		  st, [T.Branch (qs, ""); T.Cut (intro, ety, dtext)]
	    in
	    st, C.Decl (H.cic ity), rqv
	 | _, None                 ->
	    st, C.Def (H.cic v, H.cic w), [T.LetIn (intro, v, dtext)]
      in
      let entry = Some (name, hyp) in
      let qt = proc_proof (next (add st entry)) t in
      List.rev_append rqv qt      
   else
      [T.Exact (what, dtext)]
   in
   mk_preamble st what script

and proc_rel st what = 
   let _, dtext = test_depth st in
   let text = "assumption" in
   let script = [T.Exact (what, dtext ^ text)] in 
   mk_preamble st what script

and proc_mutconstruct st what = 
   let _, dtext = test_depth st in
   let script = [T.Exact (what, dtext)] in 
   mk_preamble st what script

and proc_const st what = 
   let _, dtext = test_depth st in
   let script = [T.Exact (what, dtext)] in 
   mk_preamble st what script

and proc_appl st what hd tl =
   let proceed, dtext = test_depth st in
   let script = if proceed then
      let ty = match get_inner_types st hd with
         | Some (ity, _) -> H.cic ity 
	 | None          -> get_type "TC2" st hd 
      in
      let classes, rc = Cl.classify st.context ty in
      let goal_arity, goal = match get_inner_types st what with
         | None          -> 0, None
	 | Some (ity, _) -> 
	   snd (PEH.split_with_whd (st.context, H.cic ity)), Some (H.cic ity)
      in
      let parsno, argsno = List.length classes, List.length tl in
      let decurry = parsno - argsno in
      let diff = goal_arity - decurry in
      if diff < 0 then 
         let text = Printf.sprintf "partial application: %i" diff in
	 prerr_endline ("Procedural 2: " ^ text);
	 [T.Exact (what, dtext ^ text)]
      else
      let classes = Cl.adjust st.context tl ?goal classes in
      let rec mk_synth a n =
         if n < 0 then a else mk_synth (I.S.add n a) (pred n)
      in
      let synth = mk_synth I.S.empty decurry in
      let text = if !debug
         then Printf.sprintf "%u %s" parsno (Cl.to_string synth (classes, rc))
	 else ""
      in
      let script = List.rev (mk_arg st hd) in
      let tactic b t n = if b then T.Apply (t, n) else T.Exact (t, n) in
      match rc with
         | Some (i, j, uri, tyno) when decurry = 0 ->
	    let classes2, tl2, _, where = split2_last classes tl in
	    let script2 = List.rev (mk_arg st where) @ script in
	    let synth2 = I.S.add 1 synth in
	    let names = H.get_ind_names uri tyno in
	    let qs = proc_bkd_proofs (next st) synth2 names classes2 tl2 in
            let ity = match get_inner_types st what with
                | Some (ity, _) -> ity 
                | None          -> 
		   Cn.fake_annotate "" st.context (get_type "TC3" st what)
	    in
	    if List.length qs <> List.length names then
	       let qs = proc_bkd_proofs (next st) synth [] classes tl in
	       let b, hd, qs = mk_apply_args hd tl classes synth qs in
	       script @ [tactic b hd (dtext ^ text); T.Branch (qs, "")]
	    else if is_rewrite_right st hd then 
	       script2 @ mk_rewrite st dtext where qs tl2 false what ity
	    else if is_rewrite_left st hd then 
	       script2 @ mk_rewrite st dtext where qs tl2 true what ity
	    else
	       let predicate = List.nth tl2 (parsno - i) in
               let e = Cn.mk_pattern j ity predicate in
	       let using = Some hd in
	       script2 @ 
	       [T.Elim (where, using, e, dtext ^ text); T.Branch (qs, "")]
	 | _                                       ->
	    let names = get_sub_names hd tl in
	    let qs = proc_bkd_proofs (next st) synth names classes tl in
	    let b, hd, qs = mk_apply_args hd tl classes synth qs in
	    script @ [tactic b hd (dtext ^ text); T.Branch (qs, "")]
   else
      [T.Exact (what, dtext)]
   in
   mk_preamble st what script

and proc_case st what uri tyno u v ts =
   let proceed, dtext = test_depth st in
   let script = if proceed then
      let synth, classes = I.S.empty, Cl.make ts in
      let names = H.get_ind_names uri tyno in
      let qs = proc_bkd_proofs (next st) synth names classes ts in
      let lpsno, _ = H.get_ind_type uri tyno in
      let ps, _ = H.get_ind_parameters st.context (H.cic v) in
      let _, rps = HEL.split_nth lpsno ps in
      let rpsno = List.length rps in 
      let ity = match get_inner_types st what with
         | Some (ity, _) -> ity 
         | None          -> 
	    Cn.fake_annotate "" st.context (get_type "TC4" st what)
      in
      let e = Cn.mk_pattern rpsno ity u in
      let text = "" in
      let script = List.rev (mk_arg st v) in
      script @ [T.Cases (v, e, dtext ^ text); T.Branch (qs, "")]   
   else
      [T.Exact (what, dtext)]
   in
   mk_preamble st what script

and proc_other st what =
   let _, dtext = test_depth st in
   let text = Printf.sprintf "%s: %s" "UNEXPANDED" (string_of_head what) in
   let script = [T.Exact (what, dtext ^ text)] in 
   mk_preamble st what script

and proc_proof st t = 
   let f st =
(*      
      let xtypes, note = match get_inner_types st t with
         | Some (it, et) -> Some (H.cic it, H.cic et), 
	  (Printf.sprintf "\nInferred: %s\nExpected: %s"
	  (Pp.ppterm (H.cic it)) (Pp.ppterm (H.cic et))) 
         | None          -> None, "\nNo types"
      in    
      let context, clears = Cn.get_clears st.context (H.cic t) xtypes in
      {st with context = context}
*)
      st
   in
   match t with
      | C.ALambda (_, name, w, t) as what        -> proc_lambda (f st) what name w t
      | C.ALetIn (_, name, v, w, t) as what      -> proc_letin (f st) what name v w t
      | C.ARel _ as what                         -> proc_rel (f st) what
      | C.AMutConstruct _ as what                -> proc_mutconstruct (f st) what
      | C.AConst _ as what                       -> proc_const (f st) what
      | C.AAppl (_, hd :: tl) as what            -> proc_appl (f st) what hd tl
(* FG: we deactivate the tactic "cases" because it does not work properly
      | C.AMutCase (_, uri, i, u, v, ts) as what -> proc_case (f st) what uri i u v ts
*)      
      | what                                     -> proc_other (f st) what

and proc_bkd_proofs st synth names classes ts =
try 
   let get_names b = ref (names, if b then push st else st) in
   let get_note f b names = 
      match !names with 
         | [], st       -> f st
	 | "" :: tl, st -> names := tl, st; f st
	 | hd :: tl, st -> 
	    let note = case st hd in
	    names := tl, inc st; 
	    if b then T.Note note :: f st else f st
   in
   let _, dtext = test_depth st in   
   let aux (inv, _) v =
      if I.overlaps synth inv then None else
      if I.S.is_empty inv then Some (get_note (fun st -> proc_proof st v)) else
      Some (get_note (fun _ -> [T.Exact (v, dtext ^ "dependent")]))
   in	
   let ps = T.list_map2_filter aux classes ts in
   let b = List.length ps > 1 in
   let names = get_names b in
   List.rev_map (fun f -> f b names) ps

with Invalid_argument s -> failwith ("A2P.proc_bkd_proofs: " ^ s)

(* initialization ***********************************************************)

let init ~ids_to_inner_sorts ~ids_to_inner_types params context =
   let depth_map x y = match x, y with
      | None, G.IPDepth depth -> Some depth
      | _                     -> x
   in
   {
      sorts       = ids_to_inner_sorts;
      types       = ids_to_inner_types;
      params      = params;
      max_depth   = List.fold_left depth_map None params;
      depth       = 0;
      defaults    = not (List.mem G.IPNoDefaults params);
      cr          = List.mem G.IPCR params;
      context     = context;
      case        = []
   }

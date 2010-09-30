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
module Rf   = CicRefine
module Un   = CicUniv
module Pp   = CicPp
module TC   = CicTypeChecker
module PEH  = ProofEngineHelpers
module E    = CicEnvironment
module UM   = UriManager
module D    = Deannotate
module PER  = ProofEngineReduction
module Ut   = CicUtil
module DTI  = DoubleTypeInference

(* fresh name generator *****************************************************)

let split name =
   let rec aux i =
      if i <= 0 then assert false else
      let c = name.[pred i] in
      if c >= '0' && c <= '9' then aux (pred i) 
      else Str.string_before name i, Str.string_after name i
   in
   let before, after = aux (String.length name) in
   let i = if after = "" then -1 else int_of_string after in
   before, i

let join (s, i) =
   C.Name (if i < 0 then s else s ^ string_of_int i)

let mk_fresh_name context (name, k) = 
   let rec aux i = function
      | []                            -> name, i
      | Some (C.Name s, _) :: entries ->
         let m, j = split s in
	 if m = name && j >= i then aux (succ j) entries else aux i entries
      | _ :: entries                  -> aux i entries
   in
   join (aux k context)

let mk_fresh_name does_not_occur context = function
   | C.Name s    -> mk_fresh_name context (split s)
   | C.Anonymous -> 
      if does_not_occur then C.Anonymous 
      else mk_fresh_name context (split "LOCAL")

(* helper functions *********************************************************)

let rec list_fold_right_cps g map l a = 
   match l with
      | []       -> g a
      | hd :: tl ->
         let h a = map g hd a in
         list_fold_right_cps h map tl a

let rec list_fold_left_cps g map a = function
   | []       -> g a
   | hd :: tl ->
      let h a = list_fold_left_cps g map a tl in
      map h a hd

let rec list_map_cps g map = function
   | []       -> g []
   | hd :: tl -> 
      let h hd =
         let g tl = g (hd :: tl) in
         list_map_cps g map tl	 
      in
      map h hd

let identity x = x

let compose f g x = f (g x)

let fst3 (x, _, _) = x

let refine c t =
   let error e = 
      Printf.eprintf "Ref: context: %s\n" (Pp.ppcontext c);
      Printf.eprintf "Ref: term   : %s\n" (Pp.ppterm t);
      raise e
   in
   try let t, _, _, _ = Rf.type_of_aux' [] c t Un.default_ugraph in t with 
      | Rf.RefineFailure s as e -> 
         Printf.eprintf "REFINE FAILURE: %s\n" (Lazy.force s);
	 error e
      | e                       ->
         Printf.eprintf "REFINE ERROR: %s\n" (Printexc.to_string e);
	 error e

let get_type msg c t =
   let log s =
      prerr_endline ("TC: " ^ s); 
      prerr_endline ("TC: context: " ^ Pp.ppcontext c);
      prerr_string "TC: term   : "; Ut.pp_term prerr_string [] c t;
      prerr_newline (); prerr_endline ("TC: location: " ^ msg)
   in   
   try let ty, _ = TC.type_of_aux' [] c t Un.default_ugraph in ty with
      | TC.TypeCheckerFailure s as e ->
        log ("failure: " ^ Lazy.force s); raise e        
      | TC.AssertFailure s as e      -> 
        log ("assert : " ^ Lazy.force s); raise e

let get_tail c t =
   match PEH.split_with_whd (c, t) with
      | (_, hd) :: _, _ -> hd
      | _               -> assert false

let is_prop c t =
   match get_tail c (get_type "is_prop" c t) with
      | C.Sort C.Prop -> true
      | C.Sort _      -> false
      | _             -> assert false 

let is_proof c t =
   is_prop c (get_type "is_prop" c t)

let is_sort = function
   | C.Sort _ -> true
   | _        -> false 

let is_unsafe h (c, t) = true

let is_not_atomic = function
   | C.Sort _
   | C.Rel _
   | C.Const _
   | C.Var _
   | C.MutInd _ 
   | C.MutConstruct _ -> false
   | _                -> true

let is_atomic t = not (is_not_atomic t)

let get_ind_type uri tyno =
   match E.get_obj Un.default_ugraph uri with
      | C.InductiveDefinition (tys, _, lpsno, _), _ -> lpsno, List.nth tys tyno
      | _                                           -> assert false

let get_ind_names uri tno =
try   
   let ts = match E.get_obj Un.default_ugraph uri with
      | C.InductiveDefinition (ts, _, _, _), _ -> ts 
      | _                                      -> assert false
   in
   match List.nth ts tno with
      | (_, _, _, cs) -> List.map fst cs  
with Invalid_argument _ -> failwith "get_ind_names"

let get_default_eliminator context uri tyno ty =
   let _, (name, _, _, _) = get_ind_type uri tyno in
   let ext = match get_tail context (get_type "get_def_elim" context ty) with
      | C.Sort C.Prop      -> "_ind"
      | C.Sort C.Set       -> "_rec"
      | C.Sort (C.CProp _) -> "_rect"
      | C.Sort (C.Type _)  -> "_rect"
      | t                  -> 
         Printf.eprintf "CicPPP get_default_eliminator: %s\n" (Pp.ppterm t);
         assert false
   in
   let buri = UM.buri_of_uri uri in
   let uri = UM.uri_of_string (buri ^ "/" ^ name ^ ext ^ ".con") in
   C.Const (uri, [])

let get_ind_parameters c t =
   let ty = get_type "get_ind_pars 1" c t in
   let ps = match get_tail c ty with
      | C.MutInd _                  -> []
      | C.Appl (C.MutInd _ :: args) -> args
      | _                           -> assert false
   in
   let disp = match get_tail c (get_type "get_ind_pars 2" c ty) with
      | C.Sort C.Prop -> 0
      | C.Sort _      -> 1
      | _             -> assert false
   in
   ps, disp

let cic = D.deannotate_term

let flatten_appls =
   let rec flatten_xns (uri, t) = uri, flatten_term t
   and flatten_ms = function
      | None   -> None
      | Some t -> Some (flatten_term t)
   and flatten_fix (name, i, ty, bo) =
      name, i, flatten_term ty, flatten_term bo
   and flatten_cofix (name, ty, bo) =
      name, flatten_term ty, flatten_term bo
   and flatten_term = function
      | C.Sort _ as t -> t
      | C.Implicit _ as t -> t
      | C.Rel _ as t -> t 
      | C.Const (uri, xnss) -> C.Const (uri, List.map flatten_xns xnss)
      | C.Var (uri, xnss) -> C.Var (uri, List.map flatten_xns xnss)
      | C.MutInd (uri, tyno, xnss) -> C.MutInd (uri, tyno, List.map flatten_xns xnss)
      | C.MutConstruct (uri, tyno, consno, xnss) -> C.MutConstruct (uri, tyno, consno, List.map flatten_xns xnss)
      | C.Meta (i, mss) -> C.Meta(i, List.map flatten_ms mss)
(* begin flattening *)      
      | C.Appl [t] -> flatten_term t
      | C.Appl (C.Appl ts1 :: ts2) -> flatten_term (C.Appl (ts1 @ ts2))
      | C.Appl [] -> assert false
(* end flattening *)
      | C.Appl ts -> C.Appl (List.map flatten_term ts)
      | C.Cast (te, ty) -> C.Cast (flatten_term te, flatten_term ty)
      | C.MutCase (sp, i, outty, t, pl) -> C.MutCase (sp, i, flatten_term outty, flatten_term t, List.map flatten_term pl)
      | C.Prod (n, s, t) -> C.Prod (n, flatten_term s, flatten_term t)
      | C.Lambda (n, s, t) -> C.Lambda (n, flatten_term s, flatten_term t)
      | C.LetIn (n, ty, s, t) -> C.LetIn (n, flatten_term ty, flatten_term s, flatten_term t)
      | C.Fix (i, fl) -> C.Fix (i, List.map flatten_fix fl)
      | C.CoFix (i, fl) -> C.CoFix (i, List.map flatten_cofix fl)
   in
   flatten_term

let sober ?(flatten=false) c t =
   if flatten then flatten_appls t else (assert (Ut.is_sober c t); t)

let alpha ?flatten c t1 t2 =
   let t1 = sober ?flatten c t1 in
   let t2 = sober ?flatten c t2 in
   Ut.alpha_equivalence t1 t2

let occurs c ~what ~where =
   let result = ref false in
   let equality c t1 t2 =
      let r = alpha ~flatten:true c t1 t2 in
      result := !result || r; r
   in
   let context, what, with_what = c, [what], [C.Rel 0] in
   let _ = PER.replace_lifting ~equality ~context ~what ~with_what ~where in
   !result

let name_of_uri uri tyno cno =
   let get_ind_type tys tyno =
      let s, _, _, cs = List.nth tys tyno in s, cs
   in
   match (fst (E.get_obj Un.default_ugraph uri)), tyno, cno with
      | C.Variable (s, _, _, _, _), _, _                     -> s
      | C.Constant (s, _, _, _, _), _, _                     -> s
      | C.InductiveDefinition (tys, _, _, _), Some i, None   ->
         let s, _ = get_ind_type tys i in s
      | C.InductiveDefinition (tys, _, _, _), Some i, Some j ->
         let _, cs = get_ind_type tys i in
	 let s, _ = List.nth cs (pred j) in s
      | _                                                    -> assert false

(* Ensuring Barendregt convenction ******************************************)

let rec add_entries map c = function
   | []       -> c
   | hd :: tl ->
      let sname, w = map hd in
      let entry = Some (C.Name sname, C.Decl w) in
      add_entries map (entry :: c) tl

let get_sname c i =
   try match List.nth c (pred i) with
      | Some (C.Name sname, _) -> sname
      | _                        -> assert false
   with 
      | Failure _          -> assert false
      | Invalid_argument _ -> assert false

let cic_bc c t =
   let get_fix_decl (sname, i, w, v) = sname, w in
   let get_cofix_decl (sname, w, v) = sname, w in
   let rec bc c = function
      | C.LetIn (name, v, ty, t) ->
         let dno = DTI.does_not_occur 1 t in
	 let name = mk_fresh_name dno c name in
         let entry = Some (name, C.Def (v, ty)) in
         let v, ty, t = bc c v, bc c ty, bc (entry :: c) t in
	 C.LetIn (name, v, ty, t)
      | C.Lambda (name, w, t) ->
         let dno = DTI.does_not_occur 1 t in
         let name = mk_fresh_name dno c name in
         let entry = Some (name, C.Decl w) in
         let w, t = bc c w, bc (entry :: c) t in
	 C.Lambda (name, w, t)
      | C.Prod (name, w, t) ->
         let dno = DTI.does_not_occur 1 t in
         let name = mk_fresh_name dno c name in
         let entry = Some (name, C.Decl w) in
         let w, t = bc c w, bc (entry :: c) t in
	 C.Prod (name, w, t)
      | C.Appl vs -> 
         let vs = List.map (bc c) vs in
	 C.Appl vs
      | C.MutCase (uri, tyno, u, v, ts) ->
         let u, v, ts = bc c u, bc c v, List.map (bc c) ts in
	 C.MutCase (uri, tyno, u, v, ts)
      | C.Cast (t, u) ->  
         let t, u = bc c t, bc c u in
         C.Cast (t, u)
      | C.Fix (i, fixes) ->
         let d = add_entries get_fix_decl c fixes in
	 let bc_fix (sname, i, w, v) = (sname, i, bc c w, bc d v) in
	 let fixes = List.map bc_fix fixes in
	 C.Fix (i, fixes)
      | C.CoFix (i, cofixes) ->
         let d = add_entries get_cofix_decl c cofixes in
	 let bc_cofix (sname, w, v) = (sname, bc c w, bc d v) in
	 let cofixes = List.map bc_cofix cofixes in
	 C.CoFix (i, cofixes)
      | t -> t
   in 
   bc c t

let acic_bc c t =
   let get_fix_decl (id, sname, i, w, v) = sname, cic w in
   let get_cofix_decl (id, sname, w, v) = sname, cic w in
   let rec bc c = function
      | C.ALetIn (id, name, v, ty, t) ->
         let dno = DTI.does_not_occur 1 (cic t) in
         let name = mk_fresh_name dno c name in
         let entry = Some (name, C.Def (cic v, cic ty)) in
         let v, ty, t = bc c v, bc c ty, bc (entry :: c) t in
	 C.ALetIn (id, name, v, ty, t)
      | C.ALambda (id, name, w, t) ->
         let dno = DTI.does_not_occur 1 (cic t) in      
         let name = mk_fresh_name dno c name in
         let entry = Some (name, C.Decl (cic w)) in
         let w, t = bc c w, bc (entry :: c) t in
	 C.ALambda (id, name, w, t)
      | C.AProd (id, name, w, t) ->
         let dno = DTI.does_not_occur 1 (cic t) in
         let name = mk_fresh_name dno c name in
         let entry = Some (name, C.Decl (cic w)) in
         let w, t = bc c w, bc (entry :: c) t in
	 C.AProd (id, name, w, t)
      | C.AAppl (id, vs) -> 
         let vs = List.map (bc c) vs in
	 C.AAppl (id, vs)
      | C.AMutCase (id, uri, tyno, u, v, ts) ->
         let u, v, ts = bc c u, bc c v, List.map (bc c) ts in
	 C.AMutCase (id, uri, tyno, u, v, ts)
      | C.ACast (id, t, u) ->  
         let t, u = bc c t, bc c u in
         C.ACast (id, t, u)
      | C.AFix (id, i, fixes) ->
         let d = add_entries get_fix_decl c fixes in
	 let bc_fix (id, sname, i, w, v) = (id, sname, i, bc c w, bc d v) in
	 let fixes = List.map bc_fix fixes in
	 C.AFix (id, i, fixes)
      | C.ACoFix (id, i, cofixes) ->
         let d = add_entries get_cofix_decl c cofixes in
	 let bc_cofix (id, sname, w, v) = (id, sname, bc c w, bc d v) in
	 let cofixes = List.map bc_cofix cofixes in
	 C.ACoFix (id, i, cofixes)
      | C.ARel (id1, id2, i, sname) ->
         let sname = get_sname c i in
	 C.ARel (id1, id2, i, sname)
      | t -> t
   in 
   bc c t

let is_acic_proof sorts context v =
   let id = Ut.id_of_annterm v in
   try match Hashtbl.find sorts id with
      | `Prop -> true
      | _     -> false
   with Not_found -> is_proof context (cic v)


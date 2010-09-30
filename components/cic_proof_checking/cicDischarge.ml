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

module UM = UriManager
module C  = Cic
module Un = CicUniv
module E  = CicEnvironment
module Ut = CicUtil
module TC = CicTypeChecker
module S  = CicSubstitution
module X  = HExtlib

let hashtbl_size = 11

let not_implemented =
   "discharge of current proofs is not implemented yet"

let debug = ref false

let out = prerr_string

(* helper functions *********************************************************)

let rec count_prods n = function
   | C.Prod (_, _, t) -> count_prods (succ n) t
   | _                -> n

let get_ind_type_psnos uri tyno =
   match E.get_obj Un.default_ugraph uri with
      | C.InductiveDefinition (tys, _, lpsno, _), _ -> 
         let _, _, ty, _ = List.nth tys tyno in
         lpsno, count_prods 0 ty
      | _                                           -> assert false

let typecheck b t =
   if !debug then begin
      out (Printf.sprintf "Pre Check ; %s\n" b);
      Ut.pp_term out [] [] t; out "\n";      
      let _ = TC.type_of_aux' [] [] t Un.default_ugraph in
      out (Printf.sprintf "Typecheck : %s OK\n" b)
   end

let list_pos found l =
   let rec aux n = function
      | []       -> raise Not_found
      | hd :: tl -> if found hd then n else aux (succ n) tl
   in 
   aux 0 l

let sh a b = if a == b then a else b

let rec list_map_sh map l = match l with
   | []       -> l
   | hd :: tl ->
      let hd', tl' = map hd, list_map_sh map tl in
      if hd' == hd && tl' == tl then l else
      sh hd hd' :: sh tl tl'

let flatten = function
   | C.Appl vs :: tl -> vs @ tl
   | ts              -> ts

let vars_of_uri uri =
   let obj, _ = E.get_obj Un.default_ugraph uri in
   match obj with
      | C.Constant (_, _, _, vars, _)
      | C.Variable (_, _, _, vars, _)
      | C.InductiveDefinition (_, vars, _, _)
      | C.CurrentProof (_, _, _, _, vars, _)  -> vars

let mk_arg s u =
   try List.assq u s
   with Not_found -> C.Var (u, [])

(* main functions ***********************************************************)

type status = {
   dn: string -> string;                (* name discharge map              *)
   du: UM.uri -> UM.uri;                (* uri discharge map               *)
   ls: (UM.uri, UM.uri list) Hashtbl.t; (* var lists of subobjects         *)
   rl: UM.uri list;                     (* reverse var list of this object *)
   h : int;                             (* relocation index                *)
   c : C.context                        (* local context of this object    *)
}

let add st k es = {st with h = st.h + k; c = List.rev_append es st.c}

let discharge st u = st.h + list_pos (UM.eq u) st.rl

let get_args st u =
   try Hashtbl.find st.ls u
   with Not_found -> 
      let args = vars_of_uri u in
      Hashtbl.add st.ls u args; args

let proj_fix (s, _, w, _) = s, w 

let proj_cofix (s, w, _) = s, w

let mk_context proj discharge_term s = 
   let map e = 
      let s, w = proj e in
      let w' = discharge_term w in
      Some (C.Name s, C.Decl w')      
   in
   List.length s, List.rev_map map s

let rec split_absts named no c = function
   | C.Lambda (s, w, t) -> 
      let e = Some (s, C.Decl w) in
      let named = named && s <> C.Anonymous in
      split_absts named (succ no) (e :: c) t
   | t                  ->
      named, no, c, t

let close is_type c t = 
   let map t = function
      | Some (b, C.Def (v, w)) -> C.LetIn (b, v, w, t)
      | Some (b, C.Decl w)     ->
         if is_type then C.Prod (b, w, t) else C.Lambda (b, w, t)
      | None                   -> assert false
   in
   List.fold_left map t c

let relocate to_what from_what k m =
   try 
      let u = List.nth from_what (m - k) in
      let map v m = if UM.eq u v then Some m else None in
      match X.list_findopt map to_what with      
         | Some m -> m + k
	 | None   -> raise (Failure "nth")
   with
      | Failure "nth" -> assert false

let rec discharge_term st t = match t with
   | C.Implicit _
   | C.Sort _
   | C.Rel _                      -> t
   | C.Const (u, s)               ->
      let args = get_args st u in
      if args = [] then t else
      let s = List.map (mk_arg s) args in
      C.Appl (C.Const (st.du u, []) :: discharge_nsubst st s)
   | C.MutInd (u, m, s)           ->
      let args = get_args st u in
      if args = [] then t else
      let s = List.map (mk_arg s) args in
      C.Appl (C.MutInd (st.du u, m, []) :: discharge_nsubst st s)
   | C.MutConstruct (u, m, n, s)  ->
      let args = get_args st u in
      if args = [] then t else
      let s = List.map (mk_arg s) args in
      C.Appl (C.MutConstruct (st.du u, m, n, []) :: discharge_nsubst st s)
   | C.Var (u, s)                 ->
(* We do not discharge the nsubst because variables are not closed *)
(* thus only the identity nsubst should be allowed                 *)
      if s <> [] then assert false else
      C.Rel (discharge st u)
   | C.Meta (i, s)                ->
      let s' = list_map_sh (discharge_usubst st) s in
      if s' == s then t else C.Meta (i, s')
   | C.Appl vs                    ->
      let vs' = list_map_sh (discharge_term st) vs in
      if vs' == vs then t else C.Appl (flatten vs')
   | C.Cast (v, w)                ->
      let v', w' = discharge_term st v, discharge_term st w in
      if v' == v && w' == w then t else
      C.Cast (sh v v', sh w w')
   | C.MutCase (u, m, w, v, vs)   ->
      let args = get_args st u in
      let u' = if args = [] then u else st.du u in
      let w', v', vs' = 
         discharge_term st w, discharge_term st v,
	 list_map_sh (discharge_term st) vs
      in
(* BEGIN FIX OUT TYPE  *)
      let lpsno, psno = get_ind_type_psnos u m in
      let rpsno = psno - lpsno in
      let named, frpsno, wc, wb = split_absts true 0 [] w' in
      let w' =
(* No fixing needed *)      
         if frpsno = succ rpsno then w' else
(* Fixing needed, no right parametes *)
	 if frpsno = rpsno && rpsno = 0 then
            let vty, _ = TC.type_of_aux' [] st.c v' Un.default_ugraph in
      	    if !debug then begin
	       out "VTY: "; Ut.pp_term out [] st.c vty; out "\n"
	    end;
	    C.Lambda (C.Anonymous, vty, S.lift 1 wb)
	 else
(* Fixing needed, some right parametes *)
	 if frpsno = rpsno && named then
	    let vty, _ = TC.type_of_aux' [] st.c v' Un.default_ugraph in
      	    if !debug then begin
	       out "VTY: "; Ut.pp_term out [] st.c vty; out "\n"
	    end;
	    let vty, wb = S.lift rpsno vty, S.lift 1 wb in 
	    let vty = match vty with
	       | C.Appl (C.MutInd (fu, fm, _) as hd :: args) 
	          when UM.eq fu u && fm = m && List.length args = psno ->
	          let largs, _ = X.split_nth lpsno args in
		  C.Appl (hd :: largs @ Ut.mk_rels rpsno 0)  
	       | _                                                     ->
	          assert false
	    in
	    close false wc (C.Lambda (C.Anonymous, vty, wb))
(* This case should not happen *)
	 else assert false 
      in
(* END FIX OUT TYPE  *)
      if UM.eq u u' && w' == w && v' == v && vs' == vs then t else
      C.MutCase (u', m, sh w w', sh v v', sh vs vs')
   | C.Prod (b, w, v)             ->
      let w' = discharge_term st w in 
      let es = [Some (b, C.Decl w')] in
      let v' = discharge_term (add st 1 es) v in
      if w' == w && v' == v then t else
      C.Prod (b, sh w w', sh v v')
   | C.Lambda (b, w, v)           ->
      let w' = discharge_term st w in 
      let es = [Some (b, C.Decl w')] in
      let v' = discharge_term (add st 1 es) v in
      if w' == w && v' == v then t else
      C.Lambda (b, sh w w', sh v v')
   | C.LetIn (b, y, w, v)   ->
      let y', w' = discharge_term st y, discharge_term st w in
      let es = [Some (b, C.Def (y, w'))] in
      let v' =  discharge_term (add st 1 es) v in
      if y' == y && w' == w && v' == v then t else
      C.LetIn (b, sh y y', sh w w', sh v v')
   | C.CoFix (i, s)         ->
      let no, es = mk_context proj_cofix (discharge_term st) s in
      let s' = list_map_sh (discharge_cofun st no es) s in
      if s' == s then t else C.CoFix (i, s')
   | C.Fix (i, s)         ->
      let no, es = mk_context proj_fix (discharge_term st) s in
      let s' = list_map_sh (discharge_fun st no es) s in
      if s' == s then t else C.Fix (i, s')

and discharge_nsubst st s =
   List.map (discharge_term st) s

and discharge_usubst st s = match s with
   | None   -> s
   | Some t ->
      let t' = discharge_term st t in
      if t' == t then s else Some t'

and discharge_cofun st no es f =
   let b, w, v = f in
   let w', v' = discharge_term st w, discharge_term (add st no es) v in
   if w' == w && v' == v then f else
   b, sh w w', sh v v'

and discharge_fun st no es f =
   let b, i, w, v = f in
   let w', v' = discharge_term st w, discharge_term (add st no es) v in
   if w' == w && v' == v then f else
   b, i, sh w w', sh v v'

let close is_type st = close is_type st.c

let discharge_con st con =
   let b, v = con in
   let v' = discharge_term st v in
   if v' == v && st.rl = [] then con else st.dn b, close true st (sh v v')

let discharge_type st ind_type =
   let b, ind, w, cons = ind_type in
   let w', cons' = discharge_term st w, list_map_sh (discharge_con st) cons in
   if w' == w && cons' == cons && st.rl = [] then ind_type else
   let w'' = close true st (sh w w') in
   st.dn b, ind, w'', sh cons cons'

let rec discharge_object dn du obj = 
   let ls = Hashtbl.create hashtbl_size in match obj with
   | C.Variable (b, None, w, vars, attrs)              ->
      let st = init_status dn du ls vars in
      let w' = discharge_term st w in
      if w' == w && vars = [] then obj else
      let w'' = sh w w' in
(* We do not typecheck because variables are not closed *)
      C.Variable (dn b, None, w'', vars, attrs)
   | C.Variable (b, Some v, w, vars, attrs)            ->
      let st = init_status dn du ls vars in
      let w', v' = discharge_term st w, discharge_term st v in
      if w' == w && v' == v && vars = [] then obj else
      let w'', v'' = sh w w', sh v v' in
(* We do not typecheck because variables are not closed *)
      C.Variable (dn b, Some v'', w'', vars, attrs)
   | C.Constant (b, None, w, vars, attrs)              ->
      let st = init_status dn du ls vars in
      let w' = discharge_term st w in
      if w' == w && vars = [] then obj else
      let w'' = close true st (sh w w') in
      let _ = typecheck (dn b) w'' in
      C.Constant (dn b, None, w'', [], attrs)
   | C.Constant (b, Some v, w, vars, attrs)            ->
      let st = init_status dn du ls vars in
      let w', v' = discharge_term st w, discharge_term st v in
      if w' == w && v' == v && vars = [] then obj else
      let w'', v'' = close true st (sh w w'), close false st (sh v v') in
      let _ = typecheck (dn b) (C.Cast (v'', w'')) in
      C.Constant (dn b, Some v'', w'', [], attrs)
   | C.InductiveDefinition (types, vars, lpsno, attrs) ->
      let st = init_status dn du ls vars in
      let types' = list_map_sh (discharge_type st) types in
      if types' == types && vars = [] then obj else
      let lpsno' = lpsno + List.length vars in
      C.InductiveDefinition (sh types types', [], lpsno', attrs)
   | C.CurrentProof _                                  ->
      HLog.warn not_implemented; obj

and discharge_uri dn du uri =
   let prerr msg obj =
      if !debug then begin
         out msg; Ut.pp_obj out obj; out "\n"
      end
   in
   let obj, _ = E.get_obj Un.default_ugraph uri in
   prerr "Plain     : " obj;
   let obj' = discharge_object dn du obj in
   prerr "Discharged: " obj';
   obj', obj' == obj

and discharge_vars dn du vars =
   let rec aux us c = function
      | []      -> c
      | u :: tl ->
         let e = match discharge_uri dn du u with
            | C.Variable (b, None, w, vars, _), _   -> 
	       let map = relocate us (List.rev vars) in 
	       let w = S.lift_map 1 map w in
	       Some (C.Name b, C.Decl w)
            | C.Variable (b, Some v, w, vars, _), _ -> 
	       let map = relocate us (List.rev vars) in
	       let v, w = S.lift_map 1 map v, S.lift_map 1 map w in
	       Some (C.Name b, C.Def (v, w))
	    | _                                     -> assert false
         in
       	 aux (u :: us) (e :: c) tl
   in 
   aux [] [] vars

and init_status dn du ls vars =
   let c, rl = discharge_vars dn du vars, List.rev vars in
   {dn = dn; du = du; ls = ls; rl = rl; h = 1; c = c} 

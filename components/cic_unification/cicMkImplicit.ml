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
 * http://cs.unibo.it/helm/.
 *)

(* $Id$ *)

(* identity_relocation_list_for_metavariable i canonical_context         *)
(* returns the identity relocation list, which is the list [1 ; ... ; n] *)
(* where n = List.length [canonical_context]                             *)
(*CSC: ma mi basta la lunghezza del contesto canonico!!!*)
let identity_relocation_list_for_metavariable ?(start = 1) canonical_context =
  let rec aux =
   function
      (_,[]) -> []
    | (n,None::tl) -> None::(aux ((n+1),tl))
    | (n,_::tl) -> (Some (Cic.Rel n))::(aux ((n+1),tl))
  in
   aux (start,canonical_context)

(* Returns the first meta whose number is above the *)
(* number of the higher meta.                       *)
let new_meta metasenv subst =
  let rec aux =
   function
      None, [] -> 1
    | Some n, [] -> n
    | None, n::tl -> aux (Some n,tl)
    | Some m, n::tl -> if n > m then aux (Some n,tl) else aux (Some m,tl)
  in
  let indexes = 
    (List.map (fun (i, _, _) -> i) metasenv) @ (List.map fst subst)
  in
  1 + aux (None, indexes)

(* let apply_subst_context = CicMetaSubst.apply_subst_context;; *)
(* questa o la precedente sembrano essere equivalenti come tempi *)
let apply_subst_context _ context = context ;;

let mk_implicit metasenv subst context =
  let newmeta = new_meta metasenv subst in
  let newuniv = CicUniv.fresh () in
  let irl = identity_relocation_list_for_metavariable context in
    (* in the following mk_* functions we apply substitution to canonical
    * context since we have the invariant that the metasenv has already been
    * instantiated with subst *)
  let context = apply_subst_context subst context in
  ([ newmeta, [], Cic.Sort (Cic.Type newuniv) ;
    (* TASSI: ?? *)
    newmeta + 1, context, Cic.Meta (newmeta, []);
    newmeta + 2, context, Cic.Meta (newmeta + 1,irl) ] @ metasenv,
   newmeta + 2)

let mk_implicit_type metasenv subst context =
  let newmeta = new_meta metasenv subst in
  let newuniv = CicUniv.fresh () in
  let context = apply_subst_context subst context in
  ([ newmeta, [], Cic.Sort (Cic.Type newuniv);
    (* TASSI: ?? *)
    newmeta + 1, context, Cic.Meta (newmeta, []) ] @metasenv,
   newmeta + 1)

let mk_implicit_sort metasenv subst =
  let newmeta = new_meta metasenv subst in
  let newuniv = CicUniv.fresh () in
  ([ newmeta, [], Cic.Sort (Cic.Type newuniv)] @ metasenv, newmeta)
  (* TASSI: ?? *)

let n_fresh_metas metasenv subst context n = 
  if n = 0 then metasenv, []
  else 
    let irl = identity_relocation_list_for_metavariable context in
    let context = apply_subst_context subst context in
    let newmeta = new_meta metasenv subst in
    let newuniv = CicUniv.fresh () in
    let rec aux newmeta n = 
      if n = 0 then metasenv, [] 
      else
        let metasenv', l = aux (newmeta + 3) (n-1) in 
	(* TASSI: ?? *)
        (newmeta, context, Cic.Sort (Cic.Type newuniv))::
        (newmeta + 1, context, Cic.Meta (newmeta, irl))::
        (newmeta + 2, context, Cic.Meta (newmeta + 1,irl))::metasenv',
        Cic.Meta(newmeta+2,irl)::l in
    aux newmeta n
      
let fresh_subst metasenv subst context uris = 
  let irl = identity_relocation_list_for_metavariable context in
  let context = apply_subst_context subst context in
  let newmeta = new_meta metasenv subst in
  let newuniv = CicUniv.fresh () in
  let rec aux newmeta = function
      [] -> metasenv, [] 
    | uri::tl ->
       let metasenv', l = aux (newmeta + 3) tl in 
         (* TASSI: ?? *)
	 (newmeta, context, Cic.Sort (Cic.Type newuniv))::
         (newmeta + 1, context, Cic.Meta (newmeta, irl))::
         (newmeta + 2, context, Cic.Meta (newmeta + 1,irl))::metasenv',
          (uri,Cic.Meta(newmeta+2,irl))::l in
    aux newmeta uris


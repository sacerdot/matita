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

(* $Id: proofEngineHelpers.ml 7022 2006-11-15 19:47:41Z fguidi $ *)

(* saturate_term newmeta metasenv context ty goal_arity                       *)
(* Given a type [ty] (a backbone), it returns its suffix of length            *)
(* [goal_arity] head and a new metasenv in which there is new a META for each *)
(* hypothesis, a list of arguments for the new applications and the index of  *)
(* the last new META introduced. The nth argument in the list of arguments is *)
(* just the nth new META.                                                     *)
let saturate_term ?(delta=true) newmeta metasenv context ty goal_arity =
 let module C = Cic in
 let module S = CicSubstitution in
 assert (goal_arity >= 0);
  let rec aux newmeta ty =
   match ty with
      C.Cast (he,_) -> aux newmeta he
(* CSC: patch to generate ?1 : ?2 : Type in place of ?1 : Type to simulate ?1 :< Type
      (* If the expected type is a Type, then also Set is OK ==>
      *  we accept any term of type Type *)
      (*CSC: BUG HERE: in this way it is possible for the term of
      * type Type to be different from a Sort!!! *)
    | C.Prod (name,(C.Sort (C.Type _) as s),t) ->
       (* TASSI: ask CSC if BUG HERE refers to the C.Cast or C.Propd case *)
       let irl =
         CicMkImplicit.identity_relocation_list_for_metavariable context
       in
        let newargument = C.Meta (newmeta+1,irl) in
         let (res,newmetasenv,arguments,lastmeta) =
          aux (newmeta + 2) (S.subst newargument t)
         in
          res,
           (newmeta,[],s)::(newmeta+1,context,C.Meta (newmeta,[]))::newmetasenv,
           newargument::arguments,lastmeta
*)
    | C.Prod (name,s,t) ->
       let irl =
         CicMkImplicit.identity_relocation_list_for_metavariable context
       in
        let newargument = C.Meta (newmeta,irl) in
         let res,newmetasenv,arguments,lastmeta,prod_no =
          aux (newmeta + 1) (S.subst newargument t)
         in
          if prod_no + 1 = goal_arity then
           let head = CicReduction.normalize ~delta:false context ty in
            head,[],[],newmeta,goal_arity + 1
          else
           (** NORMALIZE RATIONALE 
            * we normalize the target only NOW since we may be in this case:
            * A1 -> A2 -> T where T = (\lambda x.A3 -> P) k  
            * and we want a mesasenv with ?1:A1 and ?2:A2 and not
            * ?1, ?2, ?3 (that is the one we whould get if we start from the
            * beta-normalized A1 -> A2 -> A3 -> P **)
           let s' = CicReduction.normalize ~delta:false context s in
            res,(newmeta,context,s')::newmetasenv,newargument::arguments,
             lastmeta,prod_no + 1
    | t ->
       let head = CicReduction.normalize ~delta:false context t in
        match CicReduction.whd context head ~delta with
           C.Prod _ as head' -> aux newmeta head'
         | _ -> head,[],[],newmeta,0
  in
   (* WARNING: here we are using the invariant that above the most *)
   (* recente new_meta() there are no used metas.                  *)
   let res,newmetasenv,arguments,lastmeta,_ = aux newmeta ty in
    res,metasenv @ newmetasenv,arguments,lastmeta

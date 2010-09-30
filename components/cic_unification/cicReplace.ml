(* Copyright (C) 2000, HELM Team.
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

(* $Id: cicRefine.ml 7618 2007-09-05 10:07:39Z sacerdot $ *)

exception WhatAndWithWhatDoNotHaveTheSameLength;;

module C = Cic
module S = CicSubstitution

let replace_lifting ~equality ~context ~what ~with_what ~where =
  let find_image ctx what t =
   let rec find_image_aux =
    function
       [],[] -> raise Not_found
     | what::tl1,with_what::tl2 ->
        if equality ctx what t then with_what else find_image_aux (tl1,tl2)
     | _,_ -> raise WhatAndWithWhatDoNotHaveTheSameLength
   in
    find_image_aux (what,with_what)
  in
  let add_ctx ctx n s = (Some (n, Cic.Decl s))::ctx in
  let add_ctx1 ctx n s ty = (Some (n, Cic.Def (s,ty)))::ctx in
  let rec substaux k ctx what t =
   try
    S.lift (k-1) (find_image ctx what t)
   with Not_found ->
    match t with
      C.Rel n as t -> t
    | C.Var (uri,exp_named_subst) ->
       let exp_named_subst' =
        List.map (function (uri,t) -> uri,substaux k ctx what t) exp_named_subst
       in
        C.Var (uri,exp_named_subst')
    | C.Meta (i, l) -> 
       let l' =
        List.map
         (function
             None -> None
           | Some t -> Some (substaux k ctx what t)
         ) l
       in
        C.Meta(i,l')
    | C.Sort _ as t -> t
    | C.Implicit _ as t -> t
    | C.Cast (te,ty) -> C.Cast (substaux k ctx what te, substaux k ctx what ty)
    | C.Prod (n,s,t) ->
       C.Prod
        (n, substaux k ctx what s, substaux (k + 1) (add_ctx ctx n s) (List.map (S.lift 1) what) t)
    | C.Lambda (n,s,t) ->
       C.Lambda
        (n, substaux k ctx what s, substaux (k + 1) (add_ctx ctx n s) (List.map (S.lift 1) what) t)
    | C.LetIn (n,s,ty,t) ->
       C.LetIn
        (n, substaux k ctx what s, substaux k ctx what ty, substaux (k + 1) (add_ctx1 ctx n s ty) (List.map (S.lift 1) what) t)
    | C.Appl (he::tl) ->
       (* Invariant: no Appl applied to another Appl *)
       let tl' = List.map (substaux k ctx what) tl in
        begin
         match substaux k ctx what he with
            C.Appl l -> C.Appl (l@tl')
          | _ as he' -> C.Appl (he'::tl')
        end
    | C.Appl _ -> assert false
    | C.Const (uri,exp_named_subst) ->
       let exp_named_subst' =
        List.map (function (uri,t) -> uri,substaux k ctx what t) exp_named_subst
       in
       C.Const (uri,exp_named_subst')
    | C.MutInd (uri,i,exp_named_subst) ->
       let exp_named_subst' =
        List.map (function (uri,t) -> uri,substaux k ctx what t) exp_named_subst
       in
        C.MutInd (uri,i,exp_named_subst')
    | C.MutConstruct (uri,i,j,exp_named_subst) ->
       let exp_named_subst' =
        List.map (function (uri,t) -> uri,substaux k ctx what t) exp_named_subst
       in
        C.MutConstruct (uri,i,j,exp_named_subst')
    | C.MutCase (sp,i,outt,t,pl) ->
       C.MutCase (sp,i,substaux k ctx what outt, substaux k ctx what t,
        List.map (substaux k ctx what) pl)
    | C.Fix (i,fl) ->
       let len = List.length fl in
       let substitutedfl =
        List.map
         (fun (name,i,ty,bo) -> (* WRONG CTX *)
           (name, i, substaux k ctx what ty,
             substaux (k+len) ctx (List.map (S.lift len) what) bo)
         ) fl
       in
        C.Fix (i, substitutedfl)
    | C.CoFix (i,fl) ->
       let len = List.length fl in
       let substitutedfl =
        List.map
         (fun (name,ty,bo) -> (* WRONG CTX *)
           (name, substaux k ctx what ty,
             substaux (k+len) ctx (List.map (S.lift len) what) bo)
         ) fl
       in
        C.CoFix (i, substitutedfl)
 in
  substaux 1 context what where
;;



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

(* $Id$ *)

let rec letin_nf =
 let module C = Cic in
  function
     C.Rel _ as t -> t
   | C.Var (uri,exp_named_subst) ->
      let exp_named_subst' =
       List.map (function (uri,t) -> (uri,letin_nf t)) exp_named_subst
      in
       C.Var (uri,exp_named_subst')
   | C.Meta _ as t -> t
   | C.Sort _ as t -> t
   | C.Implicit _ as t -> t
   | C.Cast (te,ty) -> C.Cast (letin_nf te, letin_nf ty)
   | C.Prod (n,s,t) -> C.Prod (n, letin_nf s, letin_nf t)
   | C.Lambda (n,s,t) -> C.Lambda (n, letin_nf s, letin_nf t)
   | C.LetIn (n,s,_,t) -> CicSubstitution.subst (letin_nf s) t
   | C.Appl l -> C.Appl (List.map letin_nf l)
   | C.Const (uri,exp_named_subst) ->
      let exp_named_subst' =
       List.map (function (uri,t) -> (uri,letin_nf t)) exp_named_subst
      in
       C.Const (uri,exp_named_subst')
   | C.MutInd (uri,typeno,exp_named_subst) ->
      let exp_named_subst' =
       List.map (function (uri,t) -> (uri,letin_nf t)) exp_named_subst
      in
       C.MutInd (uri,typeno,exp_named_subst')
   | C.MutConstruct (uri,typeno,consno,exp_named_subst) ->
      let exp_named_subst' =
       List.map (function (uri,t) -> (uri,letin_nf t)) exp_named_subst
      in
       C.MutConstruct (uri,typeno,consno,exp_named_subst')
   | C.MutCase (sp,i,outt,t,pl) ->
      C.MutCase (sp,i,letin_nf outt, letin_nf t, List.map letin_nf pl)
   | C.Fix (i,fl) ->
      let substitutedfl =
       List.map
        (fun (name,i,ty,bo) -> (name, i, letin_nf ty, letin_nf bo))
         fl
      in
       C.Fix (i, substitutedfl)
   | C.CoFix (i,fl) ->
      let substitutedfl =
       List.map
        (fun (name,ty,bo) -> (name, letin_nf ty, letin_nf bo))
         fl
      in
       C.CoFix (i, substitutedfl)
;;

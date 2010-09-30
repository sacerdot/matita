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

(* converts annotated terms into cic terms (forgetting ids and names) *)
let rec deannotate_term =
 let module C = Cic in
  function
     C.ARel (_,_,n,_) -> C.Rel n
   | C.AVar (_,uri,exp_named_subst) ->
      let deann_exp_named_subst =
       List.map (function (uri,t) -> uri,deannotate_term t) exp_named_subst
      in
       C.Var (uri, deann_exp_named_subst)
   | C.AMeta (_,n, l) ->
      let l' =
       List.map
        (function
            None -> None
          | Some at -> Some (deannotate_term at)
        ) l
      in
       C.Meta (n, l')
   | C.ASort (_,s) -> C.Sort s
   | C.AImplicit (_, annotation) -> C.Implicit annotation
   | C.ACast (_,va,ty) -> C.Cast (deannotate_term va, deannotate_term ty)
   | C.AProd (_,name,so,ta) ->
      C.Prod (name, deannotate_term so, deannotate_term ta)
   | C.ALambda (_,name,so,ta) ->
      C.Lambda (name, deannotate_term so, deannotate_term ta)
   | C.ALetIn (_,name,so,ty,ta) ->
      C.LetIn (name, deannotate_term so, deannotate_term ty, deannotate_term ta)
   | C.AAppl (_,l) -> C.Appl (List.map deannotate_term l)
   | C.AConst (_,uri,exp_named_subst) ->
      let deann_exp_named_subst =
       List.map (function (uri,t) -> uri,deannotate_term t) exp_named_subst
      in
       C.Const (uri, deann_exp_named_subst)
   | C.AMutInd (_,uri,i,exp_named_subst) ->
      let deann_exp_named_subst =
       List.map (function (uri,t) -> uri,deannotate_term t) exp_named_subst
      in
       C.MutInd (uri,i,deann_exp_named_subst)
   | C.AMutConstruct (_,uri,i,j,exp_named_subst) ->
      let deann_exp_named_subst =
       List.map (function (uri,t) -> uri,deannotate_term t) exp_named_subst
      in
       C.MutConstruct (uri,i,j,deann_exp_named_subst)
   | C.AMutCase (_,uri,i,outtype,te,pl) ->
      C.MutCase (uri,i,deannotate_term outtype,
       deannotate_term te, List.map deannotate_term pl)
   | C.AFix (_,funno,ifl) ->
      C.Fix (funno, List.map deannotate_inductiveFun ifl)
   | C.ACoFix (_,funno,ifl) ->
      C.CoFix (funno, List.map deannotate_coinductiveFun ifl)

and deannotate_inductiveFun (_,name,index,ty,bo) =
 (name, index, deannotate_term ty, deannotate_term bo)

and deannotate_coinductiveFun (_,name,ty,bo) =
 (name, deannotate_term ty, deannotate_term bo)
;;

let deannotate_inductiveType (_, name, isinductive, arity, cons) =
 (name, isinductive, deannotate_term arity,
  List.map (fun (id,ty) -> (id,deannotate_term ty)) cons)
;;

let deannotate_conjectures =
 let module C = Cic in
  List.map
   (function 
     (_,id,acontext,con) -> 
      let context = 
       List.map 
        (function 
          | _,Some (n,(C.ADef (ate,aty))) ->
             Some(n,(C.Def(deannotate_term ate,deannotate_term aty)))
          | _,Some (n,(C.ADecl at)) -> Some (n,(C.Decl (deannotate_term at)))
          | _,None -> None)
        acontext  
      in
       (id,context,deannotate_term con))
;;

let type_of_aux' = ref (fun _ _ -> assert false);;
let lift  = ref (fun _ _ -> assert false);;

let rec compute_letin_type context te =
 let module C = Cic in
   match te with
      C.Rel _
    | C.Sort _ -> te
    | C.Implicit _ -> assert false
    | C.Meta (n,l) ->
       C.Meta (n,
        List.map
        (fun x ->
          match x with
             None -> None
           | Some x -> Some (compute_letin_type context x)) l)
    | C.Cast (te,ty) ->
       C.Cast
        (compute_letin_type context te,
         compute_letin_type context ty)
    | C.Prod (name,so,dest) ->
       let so = compute_letin_type context so in
       C.Prod (name, so,
        compute_letin_type ((Some (name,(C.Decl so)))::context) dest)
    | C.Lambda (name,so,dest) ->
       let so = compute_letin_type context so in
       C.Lambda (name, so,
        compute_letin_type ((Some (name,(C.Decl so)))::context) dest)
    | C.LetIn (name,so,C.Implicit _,dest) ->
       let so = compute_letin_type context so in
       let ty = Unshare.unshare ~fresh_univs:true (!type_of_aux' context so) in
        C.LetIn (name, so, ty,
         compute_letin_type ((Some (name,(C.Def (so,ty))))::context) dest)
    | C.LetIn (name,so,ty,dest) ->
       let so = compute_letin_type context so in
       let ty = compute_letin_type context ty in
       C.LetIn (name, so, ty,
        compute_letin_type ((Some (name,(C.Def (so,ty))))::context) dest)
    | C.Appl l ->
       C.Appl (List.map (fun x -> compute_letin_type context x) l)
    | C.Var (uri,exp_named_subst) -> 
       C.Var (uri,
        List.map (fun (u,x) -> u,compute_letin_type context x) exp_named_subst)
    | C.Const (uri,exp_named_subst) ->
       C.Const (uri,
        List.map (fun (u,x) -> u,compute_letin_type context x) exp_named_subst)
    | C.MutInd (uri,i,exp_named_subst) ->
       C.MutInd (uri,i,
        List.map (fun (u,x) -> u,compute_letin_type context x) exp_named_subst)
    | C.MutConstruct (uri,i,j,exp_named_subst) ->
       C.MutConstruct (uri,i,j,
        List.map (fun (u,x) -> u,compute_letin_type context x) exp_named_subst)
    | C.MutCase (uri,i,out,te,pl) ->
       C.MutCase (uri,i,
        compute_letin_type context out,
        compute_letin_type context te,
        List.map (fun x -> compute_letin_type context x) pl)
    | C.Fix (fno,fl) ->
        let fl =
         List.map
          (function (name,recno,ty,bo) ->
            name,recno,compute_letin_type context ty, bo) fl in
        let tys,_ =
         List.fold_left
          (fun (types,len) (n,_,ty,_) ->
             (Some (C.Name n,(C.Decl (!lift len ty)))::types,
              len+1)
	  ) ([],0) fl
        in
         C.Fix (fno,
          List.map
           (fun (name,recno,ty,bo) ->
             name, recno, ty, compute_letin_type (tys @ context) bo
           ) fl)
    | C.CoFix (fno,fl) ->
        let fl =
         List.map
          (function (name,ty,bo) ->
            name, compute_letin_type context ty, bo) fl in
        let tys,_ =
         List.fold_left
          (fun (types,len) (n,ty,_) ->
             (Some (C.Name n,(C.Decl (!lift len ty)))::types,
              len+1)
	  ) ([],0) fl
        in
         C.CoFix (fno,
          List.map
           (fun (name,ty,bo) ->
             name, ty, compute_letin_type (tys @ context) bo
           ) fl)
;;

let deannotate_obj =
 let deannotate_term t =
   compute_letin_type [] (deannotate_term t)
 in
 let module C = Cic in
  function
     C.AConstant (_, _, id, bo, ty, params, attrs) ->
      C.Constant (id,
       (match bo with None -> None | Some bo -> Some (deannotate_term bo)),
       deannotate_term ty, params, attrs)
   | C.AVariable (_, name, bo, ty, params, attrs) ->
      C.Variable (name,
       (match bo with None -> None | Some bo -> Some (deannotate_term bo)),
       deannotate_term ty, params, attrs)
   | C.ACurrentProof (_, _, name, conjs, bo, ty, params, attrs) ->
      C.CurrentProof (
       name,
       deannotate_conjectures conjs,
       deannotate_term bo,deannotate_term ty, params, attrs
      )
   | C.AInductiveDefinition (_, tys, params, parno, attrs) ->
      C.InductiveDefinition (List.map deannotate_inductiveType tys,
       params, parno, attrs)
;;

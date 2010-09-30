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

exception CannotSubstInMeta;;
exception RelToHiddenHypothesis;;
exception ReferenceToVariable;;
exception ReferenceToConstant;;
exception ReferenceToCurrentProof;;
exception ReferenceToInductiveDefinition;;

let debug = false
let debug_print =
 if debug then
  fun m  -> prerr_endline (Lazy.force m)
 else
  fun _  -> ()
;;

let lift_map k map =
 let rec liftaux k =
  let module C = Cic in
   function
      C.Rel m ->
       if m < k then
        C.Rel m
       else
        C.Rel (map k m)
    | C.Var (uri,exp_named_subst) ->
       let exp_named_subst' = 
        List.map (function (uri,t) -> (uri,liftaux k t)) exp_named_subst
       in
        C.Var (uri,exp_named_subst')
    | C.Meta (i,l) ->
       let l' =
        List.map
         (function
             None -> None
           | Some t -> Some (liftaux k t)
         ) l
       in
        C.Meta(i,l')
    | C.Sort _ as t -> t
    | C.Implicit _ as t -> t
    | C.Cast (te,ty) -> C.Cast (liftaux k te, liftaux k ty)
    | C.Prod (n,s,t) -> C.Prod (n, liftaux k s, liftaux (k+1) t)
    | C.Lambda (n,s,t) -> C.Lambda (n, liftaux k s, liftaux (k+1) t)
    | C.LetIn (n,s,ty,t) ->
       C.LetIn (n, liftaux k s, liftaux k ty, liftaux (k+1) t)
    | C.Appl l -> C.Appl (List.map (liftaux k) l)
    | C.Const (uri,exp_named_subst) ->
       let exp_named_subst' = 
        List.map (function (uri,t) -> (uri,liftaux k t)) exp_named_subst
       in
        C.Const (uri,exp_named_subst')
    | C.MutInd (uri,tyno,exp_named_subst) ->
       let exp_named_subst' = 
        List.map (function (uri,t) -> (uri,liftaux k t)) exp_named_subst
       in
        C.MutInd (uri,tyno,exp_named_subst')
    | C.MutConstruct (uri,tyno,consno,exp_named_subst) ->
       let exp_named_subst' = 
        List.map (function (uri,t) -> (uri,liftaux k t)) exp_named_subst
       in
        C.MutConstruct (uri,tyno,consno,exp_named_subst')
    | C.MutCase (sp,i,outty,t,pl) ->
       C.MutCase (sp, i, liftaux k outty, liftaux k t,
        List.map (liftaux k) pl)
    | C.Fix (i, fl) ->
       let len = List.length fl in
       let liftedfl =
        List.map
         (fun (name, i, ty, bo) -> (name, i, liftaux k ty, liftaux (k+len) bo))
          fl
       in
        C.Fix (i, liftedfl)
    | C.CoFix (i, fl) ->
       let len = List.length fl in
       let liftedfl =
        List.map
         (fun (name, ty, bo) -> (name, liftaux k ty, liftaux (k+len) bo))
          fl
       in
        C.CoFix (i, liftedfl)
 in
 liftaux k

let lift_from k n =
   lift_map k (fun _ m -> m + n)

let lift n t =
  if n = 0 then
   t
  else
   lift_from 1 n t
;;

(* subst t1 t2                                                         *)
(* substitutes [t1] for [Rel 1] in [t2]                                *)
(* if avoid_beta_redexes is true (default: false) no new beta redexes  *)
(* are generated. WARNING: the substitution can diverge when t2 is not *)
(* well typed and avoid_beta_redexes is true.                          *)
let rec subst ?(avoid_beta_redexes=false) arg =
 let rec substaux k =
  let module C = Cic in
   function
      C.Rel n as t ->
       (match n with
           n when n = k -> lift (k - 1) arg
         | n when n < k -> t
         | _            -> C.Rel (n - 1)
       )
    | C.Var (uri,exp_named_subst) ->
       let exp_named_subst' =
        List.map (function (uri,t) -> (uri,substaux k t)) exp_named_subst
       in
        C.Var (uri,exp_named_subst')
    | C.Meta (i, l) -> 
       let l' =
        List.map
         (function
             None -> None
           | Some t -> Some (substaux k t)
         ) l
       in
        C.Meta(i,l')
    | C.Sort _ as t -> t
    | C.Implicit _ as t -> t
    | C.Cast (te,ty) -> C.Cast (substaux k te, substaux k ty)
    | C.Prod (n,s,t) -> C.Prod (n, substaux k s, substaux (k + 1) t)
    | C.Lambda (n,s,t) -> C.Lambda (n, substaux k s, substaux (k + 1) t)
    | C.LetIn (n,s,ty,t) ->
       C.LetIn (n, substaux k s, substaux k ty, substaux (k + 1) t)
    | C.Appl (he::tl) ->
       (* Invariant: no Appl applied to another Appl *)
       let tl' = List.map (substaux k) tl in
        begin
         match substaux k he with
            C.Appl l -> C.Appl (l@tl')
            (* Experimental *)
          | C.Lambda (_,_,bo) when avoid_beta_redexes ->
             (match tl' with
                 [] -> assert false
               | [he] -> subst ~avoid_beta_redexes he bo
               | he::tl -> C.Appl (subst he bo::tl))
          | _ as he' -> C.Appl (he'::tl')
        end
    | C.Appl _ -> assert false
    | C.Const (uri,exp_named_subst)  ->
       let exp_named_subst' =
        List.map (function (uri,t) -> (uri,substaux k t)) exp_named_subst
       in
        C.Const (uri,exp_named_subst')
    | C.MutInd (uri,typeno,exp_named_subst) ->
       let exp_named_subst' =
        List.map (function (uri,t) -> (uri,substaux k t)) exp_named_subst
       in
        C.MutInd (uri,typeno,exp_named_subst')
    | C.MutConstruct (uri,typeno,consno,exp_named_subst) ->
       let exp_named_subst' =
        List.map (function (uri,t) -> (uri,substaux k t)) exp_named_subst
       in
        C.MutConstruct (uri,typeno,consno,exp_named_subst')
    | C.MutCase (sp,i,outt,t,pl) ->
       C.MutCase (sp,i,substaux k outt, substaux k t,
        List.map (substaux k) pl)
    | C.Fix (i,fl) ->
       let len = List.length fl in
       let substitutedfl =
        List.map
         (fun (name,i,ty,bo) -> (name, i, substaux k ty, substaux (k+len) bo))
          fl
       in
        C.Fix (i, substitutedfl)
    | C.CoFix (i,fl) ->
       let len = List.length fl in
       let substitutedfl =
        List.map
         (fun (name,ty,bo) -> (name, substaux k ty, substaux (k+len) bo))
          fl
       in
        C.CoFix (i, substitutedfl)
 in
  substaux 1
;;

(*CSC: i controlli di tipo debbono essere svolti da destra a             *)
(*CSC: sinistra: i{B/A;b/a} ==> a{B/A;b/a} ==> a{b/a{B/A}} ==> b         *)
(*CSC: la sostituzione ora e' implementata in maniera simultanea, ma     *)
(*CSC: dovrebbe diventare da sinistra verso destra:                      *)
(*CSC: t{a=a/A;b/a} ==> \H:a=a.H{b/a} ==> \H:b=b.H                       *)
(*CSC: per la roba che proviene da Coq questo non serve!                 *)
let subst_vars exp_named_subst t =
(*
debug_print (lazy ("@@@POSSIBLE BUG: SUBSTITUTION IS NOT SIMULTANEOUS")) ;
*)
 let rec substaux k =
  let module C = Cic in
   function
      C.Rel _ as t -> t
    | C.Var (uri,exp_named_subst') ->
       (try
         let (_,arg) =
          List.find
           (function (varuri,_) -> UriManager.eq uri varuri) exp_named_subst
         in
          lift (k -1) arg
        with
         Not_found ->
          let params =
           let obj,_ = CicEnvironment.get_obj CicUniv.empty_ugraph uri in
           (match obj with
               C.Constant _ -> raise ReferenceToConstant
             | C.Variable (_,_,_,params,_) -> params
             | C.CurrentProof _ -> raise ReferenceToCurrentProof
             | C.InductiveDefinition _ -> raise ReferenceToInductiveDefinition
           )
          in
           let exp_named_subst'' =
            substaux_in_exp_named_subst uri k exp_named_subst' params
           in
            C.Var (uri,exp_named_subst'')
       )
    | C.Meta (i, l) -> 
       let l' =
        List.map
         (function
             None -> None
           | Some t -> Some (substaux k t)
         ) l
       in
        C.Meta(i,l')
    | C.Sort _ as t -> t
    | C.Implicit _ as t -> t
    | C.Cast (te,ty) -> C.Cast (substaux k te, substaux k ty)
    | C.Prod (n,s,t) -> C.Prod (n, substaux k s, substaux (k + 1) t)
    | C.Lambda (n,s,t) -> C.Lambda (n, substaux k s, substaux (k + 1) t)
    | C.LetIn (n,s,ty,t) ->
       C.LetIn (n, substaux k s, substaux k ty, substaux (k + 1) t)
    | C.Appl (he::tl) ->
       (* Invariant: no Appl applied to another Appl *)
       let tl' = List.map (substaux k) tl in
        begin
         match substaux k he with
            C.Appl l -> C.Appl (l@tl')
          | _ as he' -> C.Appl (he'::tl')
        end
    | C.Appl _ -> assert false
    | C.Const (uri,exp_named_subst')  ->
       let params =
        let obj,_ = CicEnvironment.get_obj CicUniv.empty_ugraph uri in
        (match obj with
            C.Constant (_,_,_,params,_) -> params
          | C.Variable _ -> raise ReferenceToVariable
          | C.CurrentProof (_,_,_,_,params,_) -> params
          | C.InductiveDefinition _ -> raise ReferenceToInductiveDefinition
        )
       in
        let exp_named_subst'' =
         substaux_in_exp_named_subst uri k exp_named_subst' params
        in
         C.Const (uri,exp_named_subst'')
    | C.MutInd (uri,typeno,exp_named_subst') ->
       let params =
        let obj,_ = CicEnvironment.get_obj CicUniv.empty_ugraph uri in
        (match obj with
            C.Constant _ -> raise ReferenceToConstant
          | C.Variable _ -> raise ReferenceToVariable
          | C.CurrentProof _ -> raise ReferenceToCurrentProof
          | C.InductiveDefinition (_,params,_,_) -> params
        )
       in
        let exp_named_subst'' =
         substaux_in_exp_named_subst uri k exp_named_subst' params
        in
         C.MutInd (uri,typeno,exp_named_subst'')
    | C.MutConstruct (uri,typeno,consno,exp_named_subst') ->
       let params =
        let obj,_ = CicEnvironment.get_obj CicUniv.empty_ugraph uri in
        (match obj with
            C.Constant _ -> raise ReferenceToConstant
          | C.Variable _ -> raise ReferenceToVariable
          | C.CurrentProof _ -> raise ReferenceToCurrentProof
          | C.InductiveDefinition (_,params,_,_) -> params
        )
       in
        let exp_named_subst'' =
         substaux_in_exp_named_subst uri k exp_named_subst' params
        in
if (List.map fst exp_named_subst'' <> List.map fst (List.filter (fun (uri,_) -> List.mem uri params) exp_named_subst) @ List.map fst exp_named_subst') then (
debug_print (lazy "\n\n---- BEGIN ") ;
debug_print (lazy ("----params: " ^ String.concat " ; " (List.map UriManager.string_of_uri params))) ;
debug_print (lazy ("----S(" ^ UriManager.string_of_uri uri ^ "): " ^ String.concat " ; " (List.map (function (uri,_) -> UriManager.string_of_uri uri) exp_named_subst))) ;
debug_print (lazy ("----P: " ^ String.concat " ; " (List.map (function (uri,_) -> UriManager.string_of_uri uri) exp_named_subst'))) ;
debug_print (lazy ("----D: " ^ String.concat " ; " (List.map (function (uri,_) -> UriManager.string_of_uri uri) exp_named_subst''))) ;
debug_print (lazy "---- END\n\n ") ;
);
         C.MutConstruct (uri,typeno,consno,exp_named_subst'')
    | C.MutCase (sp,i,outt,t,pl) ->
       C.MutCase (sp,i,substaux k outt, substaux k t,
        List.map (substaux k) pl)
    | C.Fix (i,fl) ->
       let len = List.length fl in
       let substitutedfl =
        List.map
         (fun (name,i,ty,bo) -> (name, i, substaux k ty, substaux (k+len) bo))
          fl
       in
        C.Fix (i, substitutedfl)
    | C.CoFix (i,fl) ->
       let len = List.length fl in
       let substitutedfl =
        List.map
         (fun (name,ty,bo) -> (name, substaux k ty, substaux (k+len) bo))
          fl
       in
        C.CoFix (i, substitutedfl)
 and substaux_in_exp_named_subst uri k exp_named_subst' params =
  let rec filter_and_lift =
   function
      [] -> []
    | (uri,t)::tl when
        List.for_all
         (function (uri',_) -> not (UriManager.eq uri uri')) exp_named_subst'
        &&
         List.mem uri params
       ->
        (uri,lift (k-1) t)::(filter_and_lift tl)
    | _::tl -> filter_and_lift tl
  in
   let res =
    List.map (function (uri,t) -> (uri,substaux k t)) exp_named_subst' @
     (filter_and_lift exp_named_subst)
   in
    let rec reorder =
     function
        [] -> []
      | uri::tl ->
         let he =
          try
           [uri,List.assoc uri res]
          with
           Not_found -> []
         in
          he@reorder tl
    in
     reorder params
 in
  if exp_named_subst = [] then t
  else substaux 1 t
;;

(* subst_meta [t_1 ; ... ; t_n] t                                *)
(* returns the term [t] where [Rel i] is substituted with [t_i] *)
(* [t_i] is lifted as usual when it crosses an abstraction      *)
let subst_meta l t = 
 let module C = Cic in
  if l = [] then t else 
   let rec aux k = function
      C.Rel n as t -> 
        if n <= k then t else 
         (try
           match List.nth l (n-k-1) with
              None -> raise RelToHiddenHypothesis
            | Some t -> lift k t
          with
           (Failure _) -> assert false
         )
    | C.Var (uri,exp_named_subst) ->
       let exp_named_subst' =
        List.map (function (uri,t) -> (uri,aux k t)) exp_named_subst
       in
        C.Var (uri,exp_named_subst')
    | C.Meta (i,l) ->
       let l' =
        List.map
         (function
             None -> None
           | Some t ->
              try
               Some (aux k t)
              with
               RelToHiddenHypothesis -> None
         ) l
       in
        C.Meta(i,l')
    | C.Sort _ as t -> t
    | C.Implicit _ as t -> t
    | C.Cast (te,ty) -> C.Cast (aux k te, aux k ty) (*CSC ??? *)
    | C.Prod (n,s,t) -> C.Prod (n, aux k s, aux (k + 1) t)
    | C.Lambda (n,s,t) -> C.Lambda (n, aux k s, aux (k + 1) t)
    | C.LetIn (n,s,ty,t) -> C.LetIn (n, aux k s, aux k ty, aux (k + 1) t)
    | C.Appl l -> C.Appl (List.map (aux k) l)
    | C.Const (uri,exp_named_subst) ->
       let exp_named_subst' =
        List.map (function (uri,t) -> (uri,aux k t)) exp_named_subst
       in
        C.Const (uri,exp_named_subst')
    | C.MutInd (uri,typeno,exp_named_subst) ->
       let exp_named_subst' =
        List.map (function (uri,t) -> (uri,aux k t)) exp_named_subst
       in
        C.MutInd (uri,typeno,exp_named_subst')
    | C.MutConstruct (uri,typeno,consno,exp_named_subst) ->
       let exp_named_subst' =
        List.map (function (uri,t) -> (uri,aux k t)) exp_named_subst
       in
        C.MutConstruct (uri,typeno,consno,exp_named_subst')
    | C.MutCase (sp,i,outt,t,pl) ->
       C.MutCase (sp,i,aux k outt, aux k t, List.map (aux k) pl)
    | C.Fix (i,fl) ->
       let len = List.length fl in
       let substitutedfl =
        List.map
         (fun (name,i,ty,bo) -> (name, i, aux k ty, aux (k+len) bo))
          fl
       in
        C.Fix (i, substitutedfl)
    | C.CoFix (i,fl) ->
       let len = List.length fl in
       let substitutedfl =
        List.map
         (fun (name,ty,bo) -> (name, aux k ty, aux (k+len) bo))
          fl
       in
        C.CoFix (i, substitutedfl)
 in
  aux 0 t          
;;

Deannotate.lift := lift;;

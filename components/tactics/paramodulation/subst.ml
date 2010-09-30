(* cOpyright (C) 2005, HELM Team.
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

(* $Id: inference.ml 6245 2006-04-05 12:07:51Z tassi $ *)


(******* CIC substitution ***************************************************)

type cic_substitution = Cic.substitution
let cic_apply_subst = CicMetaSubst.apply_subst
let cic_apply_subst_metasenv = CicMetaSubst.apply_subst_metasenv
let cic_ppsubst = CicMetaSubst.ppsubst
let cic_buildsubst n context t ty tail = (n,(context,t,ty)) :: tail
let cic_flatten_subst subst =
    List.map
      (fun (i, (context, term, ty)) ->
         let context = (* cic_apply_subst_context subst*) context in
         let term = cic_apply_subst subst term in
         let ty = cic_apply_subst subst ty in  
         (i, (context, term, ty))) subst
let rec cic_lookup_subst meta subst =
  match meta with
  | Cic.Meta (i, _) -> (
      try let _, (_, t, _) = List.find (fun (m, _) -> m = i) subst 
      in cic_lookup_subst t subst 
      with Not_found -> meta
    )
  | _ -> meta
;;

let cic_merge_subst_if_possible s1 s2 =
  let already_in = Hashtbl.create 13 in
  let rec aux acc = function
    | ((i,_,x) as s)::tl ->
        (try 
          let x' = Hashtbl.find already_in i in
          if x = x' then aux acc tl else None
        with
        | Not_found -> 
            Hashtbl.add already_in i x;
            aux (s::acc) tl)
    | [] -> Some acc 
  in  
    aux [] (s1@s2)
;;

(******** NAIF substitution **************************************************)
(* 
 * naif version of apply subst; the local context of metas is ignored;
 * we assume the substituted term must be lifted according to the nesting
 * depth of the meta. 
 * Alternatively, we could used implicit instead of metas 
 *)

type naif_substitution = (int * Cic.term) list 

let naif_apply_subst lift subst term =
 let rec aux k t =
   match t with
       Cic.Rel _ -> t
     | Cic.Var (uri,exp_named_subst) -> 
         let exp_named_subst' =
           List.map (fun (uri, t) -> (uri, aux k t)) exp_named_subst
         in
           Cic.Var (uri, exp_named_subst')
    | Cic.Meta (i, l) -> 
        (try
          aux k (CicSubstitution.lift (k+lift) (List.assoc i subst)) 
         with Not_found -> t)
    | Cic.Sort _
    | Cic.Implicit _ -> t
    | Cic.Cast (te,ty) -> Cic.Cast (aux k te, aux k ty)
    | Cic.Prod (n,s,t) -> Cic.Prod (n, aux k s, aux (k+1) t)
    | Cic.Lambda (n,s,t) -> Cic.Lambda (n, aux k s, aux (k+1) t)
    | Cic.LetIn (n,s,ty,t) -> Cic.LetIn (n, aux k s, aux k ty, aux (k+1) t)
    | Cic.Appl [] -> assert false
    | Cic.Appl l -> Cic.Appl (List.map (aux k) l)
    | Cic.Const (uri,exp_named_subst) ->
        let exp_named_subst' =
          List.map (fun (uri, t) -> (uri, aux k t)) exp_named_subst
        in
          if exp_named_subst' != exp_named_subst then
            Cic.Const (uri, exp_named_subst')
          else
            t (* TODO: provare a mantenere il piu' possibile sharing *)
    | Cic.MutInd (uri,typeno,exp_named_subst) ->
        let exp_named_subst' =
          List.map (fun (uri, t) -> (uri, aux k t)) exp_named_subst
        in
          Cic.MutInd (uri,typeno,exp_named_subst')
    | Cic.MutConstruct (uri,typeno,consno,exp_named_subst) ->
        let exp_named_subst' =
          List.map (fun (uri, t) -> (uri, aux k t)) exp_named_subst
        in
          Cic.MutConstruct (uri,typeno,consno,exp_named_subst')
    | Cic.MutCase (sp,i,outty,t,pl) ->
        let pl' = List.map (aux k) pl in
          Cic.MutCase (sp, i, aux k outty, aux k t, pl')
    | Cic.Fix (i, fl) ->
        let len = List.length fl in
        let fl' =
         List.map 
           (fun (name, i, ty, bo) -> (name, i, aux k ty, aux (k+len) bo)) fl
        in
          Cic.Fix (i, fl')
    | Cic.CoFix (i, fl) ->
        let len = List.length fl in
        let fl' =
          List.map (fun (name, ty, bo) -> (name, aux k ty, aux (k+len) bo)) fl
        in
          Cic.CoFix (i, fl')
in
  aux 0 term
;;

(* naif version of apply_subst_metasenv: we do not apply the 
substitution to the context *)

let naif_apply_subst_metasenv subst metasenv =
  List.map
    (fun (n, context, ty) ->
      (n, context, naif_apply_subst 0 subst ty))
    (List.filter
      (fun (i, _, _) -> not (List.mem_assoc i subst))
      metasenv)

let naif_ppsubst names subst =
  "{" ^ String.concat "; "
    (List.map
      (fun (idx, t) ->
         Printf.sprintf "%d:= %s" idx (CicPp.pp t names))
    subst) ^ "}"
;;

let naif_buildsubst n context t ty tail = (n,t) :: tail ;;

let naif_flatten_subst subst = 
  List.map (fun (i,t) -> i, naif_apply_subst 0 subst t ) subst
;;

let rec naif_lookup_subst meta subst =
  match meta with
    | Cic.Meta (i, _) ->
        (try
          naif_lookup_subst (List.assoc i subst) subst
        with
            Not_found -> meta)
    | _ -> meta
;;

let naif_merge_subst_if_possible s1 s2 =
  let already_in = Hashtbl.create 13 in
  let rec aux acc = function
    | ((i,x) as s)::tl ->
        (try 
          let x' = Hashtbl.find already_in i in
          if x = x' then aux acc tl else None
        with
        | Not_found -> 
            Hashtbl.add already_in i x;
            aux (s::acc) tl)
    | [] -> Some acc 
  in  
    aux [] (s1@s2)
;;

(********** ACTUAL SUBSTITUTION IMPLEMENTATION *******************************)

type substitution = naif_substitution
let apply_subst = naif_apply_subst 0
let apply_subst_lift = naif_apply_subst
let apply_subst_metasenv = naif_apply_subst_metasenv
let ppsubst ?(names=[]) l = naif_ppsubst names l
let buildsubst = naif_buildsubst
let flatten_subst = naif_flatten_subst
let lookup_subst = naif_lookup_subst

(* filter out from metasenv the variables in substs *)
let filter subst metasenv =
  List.filter
    (fun (m, _, _) ->
         try let _ = List.find (fun (i, _) -> m = i) subst in false
         with Not_found -> true)
    metasenv
;;

let is_in_subst i subst = List.mem_assoc i subst;;
  
let merge_subst_if_possible = naif_merge_subst_if_possible;;

let empty_subst = [];;

let concat x y = x @ y;;



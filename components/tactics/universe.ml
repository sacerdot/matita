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

module Codomain = struct 
  type t = Cic.term 
  let compare = Pervasives.compare 
end
module S = Set.Make(Codomain)
module TI = Discrimination_tree.Make(Cic_indexable.CicIndexable)(S)
type universe = TI.t

let empty = TI.empty ;;

let iter u f = 
  TI.iter u 
   (fun p s -> f p (S.elements s))
;;

let get_candidates univ ty = 
  S.elements (TI.retrieve_unifiables univ ty)
;;

let in_universe univ ty =
  let candidates = get_candidates univ ty in
    List.fold_left 
      (fun res cand ->
	 match res with
	   | Some found -> Some found
	   | None -> 
	       let candty,_ = 
		 CicTypeChecker.type_of_aux' [] [] cand CicUniv.oblivion_ugraph in
	       let same ,_ = 
		 CicReduction.are_convertible [] candty ty CicUniv.oblivion_ugraph in
	       if same then Some cand else None
      ) None candidates
;;

let rec unfold context = function
  | Cic.Prod(name,s,t) -> 
      let t' = unfold ((Some (name,Cic.Decl s))::context) t in
        Cic.Prod(name,s,t')        
  | t -> ProofEngineReduction.unfold context t

let rec collapse_head_metas t = 
  match t with
    | Cic.Appl([]) -> assert false
    | Cic.Appl(a::l) -> 
	let a' = collapse_head_metas a in
	  (match a' with
	     | Cic.Meta(n,m) -> Cic.Meta(n,m)
	     | t -> 	
		 let l' = List.map collapse_head_metas l in
		   Cic.Appl(t::l'))
    | Cic.Rel _ 
    | Cic.Var _	 
    | Cic.Meta _ 
    | Cic.Sort _ 
    | Cic.Implicit _
    | Cic.Const _ 
    | Cic.MutInd _
    | Cic.MutConstruct _ -> t
    | Cic.LetIn _
    | Cic.Lambda _
    | Cic.Prod _
    | Cic.Cast _
    | Cic.MutCase _
    | Cic.Fix _
    | Cic.CoFix _ -> Cic.Meta(-1,[])
;;

let rec dummies_of_coercions = 
  function
    | Cic.Appl (c::l) when CoercDb.is_a_coercion c <> None ->
        Cic.Meta (-1,[])
    | Cic.Appl l -> 
        let l' = List.map dummies_of_coercions l in Cic.Appl l'
    | Cic.Lambda(n,s,t) ->
        let s' = dummies_of_coercions s in
        let t' = dummies_of_coercions t in
          Cic.Lambda (n,s',t')
    | Cic.Prod(n,s,t) ->
        let s' = dummies_of_coercions s in
        let t' = dummies_of_coercions t in
          Cic.Prod (n,s',t')        
    | Cic.LetIn(n,s,ty,t) ->
        let s' = dummies_of_coercions s in
        let ty' = dummies_of_coercions ty in
        let t' = dummies_of_coercions t in
          Cic.LetIn (n,s',ty',t')        
    | Cic.MutCase _ -> Cic.Meta (-1,[])
    | t -> t
;;


let rec head remove_coercions t = 
  let clean_up t =
    if remove_coercions then dummies_of_coercions t
    else t in
  let rec aux = function
  | Cic.Prod(_,_,t) -> 
      CicSubstitution.subst (Cic.Meta (-1,[])) (aux t)
  | t -> t
  in collapse_head_metas (clean_up (aux t))
;;


let index univ key term =
  (* flexible terms are not indexed *)
  if key = Cic.Meta(-1,[]) then univ
  else
    ((*prerr_endline("ADD: "^CicPp.ppterm key^" |-> "^CicPp.ppterm term);*)
     TI.index univ key term)
;;

let keys context ty =
  try
    [head true ty; head true (unfold context ty)]
  with ProofEngineTypes.Fail _ -> [head true ty]

let key term = head false term;;

let index_term_and_unfolded_term univ context t ty =
  let key = head true ty in
  let univ = index univ key t in
  try  
    let key = head true (unfold context ty) in
    index univ key t
  with ProofEngineTypes.Fail _ -> univ
;;

let index_local_term univ context t ty =
  let key = head true ty in
  let univ = index univ key t in
  let key1 = head false ty in
  let univ =
    if key<>key1 then index univ key1 t else univ in
  try  
    let key = head true (unfold context ty) in
    index univ key t
  with ProofEngineTypes.Fail _ -> univ
;;


let index_list univ context terms_and_types =
  List.fold_left  
    (fun acc (term,ty) -> 
       index_term_and_unfolded_term acc context term ty)
    univ terms_and_types

;;

let remove univ context term ty =
  let key = head true ty in
  let univ = TI.remove_index univ key term in
  try  
    let key = head true (unfold context ty) in
    TI.remove_index univ key term
  with ProofEngineTypes.Fail _ -> univ

let remove_uri univ uri =
  let term = CicUtil.term_of_uri uri in
  let ty,_ = CicTypeChecker.type_of_aux' [] [] term CicUniv.oblivion_ugraph in
    remove univ [] term ty



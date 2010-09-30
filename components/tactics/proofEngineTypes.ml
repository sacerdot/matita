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

(* $Id$ *)

  (**
    current proof (proof uri * metas * (in)complete proof * term to be prooved)
  *)
type proof = 
  UriManager.uri option * Cic.metasenv * Cic.substitution * Cic.term Lazy.t * Cic.term * Cic.attribute list
  (** current goal, integer index *)
type goal = int
type status = proof * goal

let initial_status ty metasenv attrs =
  let rec aux max = function
    | [] -> max + 1
    | (idx, _, _) :: tl ->
        if idx > max then
          aux idx tl
        else
          aux max tl
  in
  let newmeta_idx = aux 0 metasenv in
  let _subst = [] in
  let proof =
    None, (newmeta_idx, [], ty) :: metasenv, _subst, 
    lazy (Cic.Meta (newmeta_idx, [])), ty, attrs
  in
  (proof, newmeta_idx)

  (**
    a tactic: make a transition from one status to another one or, usually,
    raise a "Fail" (@see Fail) exception in case of failure
  *)
  (** an unfinished proof with the optional current goal *)
type tactic = status -> proof * goal list

  (** creates an opaque tactic from a status->proof*goal list function *)
let mk_tactic t = t

type reduction = Cic.context -> Cic.term -> Cic.term

let const_lazy_term t =
  (fun _ metasenv ugraph -> t, metasenv, ugraph)

type lazy_reduction =
  Cic.context -> Cic.metasenv -> CicUniv.universe_graph ->
    reduction * Cic.metasenv * CicUniv.universe_graph

let const_lazy_reduction red =
  (fun _ metasenv ugraph -> red, metasenv, ugraph)

type ('term, 'lazy_term) pattern =
  'lazy_term option * (string * 'term) list * 'term option

type lazy_pattern = (Cic.term, Cic.lazy_term) pattern

let hole = Cic.Implicit (Some `Hole)

let conclusion_pattern t =
  let t' = 
    match t with
    | None -> None
    | Some t -> Some (const_lazy_term t)
  in
  t',[], Some hole

  (** tactic failure *)
exception Fail of string Lazy.t

  (** 
    calls the opaque tactic on the status
  *)
let apply_tactic t status = 
  let (uri,metasenv,subst,bo,ty, attrs), gl = t status in
  match 
    CicRefine.pack_coercion_obj 
      (Cic.CurrentProof ("",metasenv,Cic.Rel ~-1,ty,[],attrs))
  with
  | Cic.CurrentProof (_,metasenv,_,ty,_, attrs) -> 
      (uri,metasenv,subst,bo,ty, attrs), gl
  | _ -> assert false
;;

  (** constraint: the returned value will always be constructed by Cic.Name **)
type mk_fresh_name_type =
 Cic.metasenv -> Cic.context -> Cic.name -> typ:Cic.term -> Cic.name

let goals_of_proof (_,metasenv,_subst,_,_,_) = List.map (fun (g,_,_) -> g) metasenv


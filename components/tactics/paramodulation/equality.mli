(* Copyright (C) 2006, HELM Team.
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
 * http://helm.cs.unibo.it/
 *)

type rule = SuperpositionRight | SuperpositionLeft | Demodulation

(* every equality group has its own bag. the bag contains the infos necessary
 * for building the proof. FIXME: should also contain maxmeta! *)
type equality_bag

val mk_equality_bag: unit -> equality_bag

type equality 

and proof =
    Exact of Cic.term
  | Step of Subst.substitution * (rule * int * (Utils.pos * int) * Cic.term)

and goal_proof = (rule * Utils.pos * int * Subst.substitution * Cic.term) list

type goal = goal_proof * Cic.metasenv * Cic.term

val pp_proof: 
  equality_bag ->
  (Cic.name option) list -> goal_proof -> proof -> Subst.substitution -> int ->
    Cic.term -> string

val draw_proof:
  equality_bag ->
  (Cic.name option) list -> goal_proof -> proof -> int -> unit

val pp_proofterm: Cic.term -> string

val mk_eq_ind : 
    UriManager.uri ->
    Cic.term ->
    Cic.term -> 
    Cic.term -> 
    Cic.term -> 
    Cic.term -> 
    Cic.term -> 
    Cic.term
    
val mk_equality :
  equality_bag -> int * proof * 
  (Cic.term * Cic.term * Cic.term * Utils.comparison) *
  Cic.metasenv -> equality_bag * equality

val mk_tmp_equality :
 int * (Cic.term * Cic.term * Cic.term * Utils.comparison) * Cic.metasenv -> 
    equality
    
val open_equality :
  equality ->
    int * proof * 
    (Cic.term * Cic.term * Cic.term * Utils.comparison) *
    Cic.metasenv * int
val depend : equality_bag -> equality -> int -> bool
val compare : equality -> equality -> int
val max_weight_in_proof : equality_bag -> int -> proof -> int
val max_weight : equality_bag -> goal_proof -> proof -> int
val string_of_equality : 
  ?env:Utils.environment -> equality -> string
val string_of_proof : 
  ?names:(Cic.name option)list -> equality_bag -> proof -> goal_proof -> string
(* given a proof and a list of meta indexes we are interested in the
 * instantiation gives back the cic proof and the list of instantiations *)  
(* build_goal_proof [eq_URI] [goal_proof] [initial_proof] [ty] 
 *  [ty] is the type of the goal *)
val build_goal_proof: 
  ?contextualize:bool -> 
  ?forward:bool ->
  equality_bag ->
  UriManager.uri -> goal_proof -> proof -> Cic.term-> int list -> 
    Cic.context -> Cic.metasenv -> 
    Cic.term * Cic.term list
val build_proof_term :
  equality_bag ->
  UriManager.uri -> (int * Cic.term) list -> int -> proof -> Cic.term
val refl_proof: UriManager.uri -> Cic.term -> Cic.term -> Cic.term 
(** ensures that metavariables in equality are unique *)
val fix_metas_goal: equality_bag -> goal -> equality_bag * goal
val fix_metas: equality_bag -> equality -> equality_bag * equality
val metas_of_proof: equality_bag -> proof -> int list

(* this should be used _only_ to apply (efficiently) this subst on the 
 * initial proof passed to build_goal_proof *)
val add_subst : Subst.substitution -> proof -> proof
exception TermIsNotAnEquality;;

(**
   raises TermIsNotAnEquality if term is not an equation.
   The first Cic.term is a proof of the equation
*)
val equality_of_term: 
   equality_bag -> Cic.term -> Cic.term -> Cic.metasenv ->
    equality_bag * equality

(**
   Re-builds the term corresponding to this equality
*)
val term_of_equality: UriManager.uri -> equality -> Cic.term
val term_is_equality: Cic.term -> bool

val saturate_term : 
     equality_bag -> Cic.metasenv -> Cic.substitution -> Cic.context -> Cic.term ->
         equality_bag * Cic.term * Cic.metasenv * Cic.term list

val push_maxmeta : equality_bag -> int -> equality_bag 
val maxmeta : equality_bag -> int 
val filter_metasenv_gt_maxmeta: equality_bag -> Cic.metasenv -> Cic.metasenv

(** tests a sort of alpha-convertibility between the two terms, but on the
    metavariables *)
val meta_convertibility: Cic.term -> Cic.term -> bool

(** meta convertibility between two equations *)
val meta_convertibility_eq: equality -> equality -> bool
val meta_convertibility_subst: 
  Cic.term -> Cic.term -> Cic.metasenv -> Cic.substitution option

val is_weak_identity: equality -> bool
val is_identity: Utils.environment -> equality -> bool

val is_in: equality_bag -> int -> bool

(* symmetric [eq_ty] [l] [id] [uri] [m] 
 *
 * given an equality (_,p,(_,[l],r,_),[m],[id]) of 'type' l=r
 * returns the proof of the symmetric (r=l).
 *
 * [uri] is the uri of eq
 * [eq_ty] the ty of the equality sides
 *)
val symmetric:
  equality_bag -> Cic.term -> Cic.term -> int -> UriManager.uri ->
    Cic.metasenv -> equality_bag * proof

(* takes 3 lists of alive ids (they are threated the same way, the type is
 * funny just to not oblige you to concatenate them) and drops all the dead
 * equalities *)
val collect: equality_bag -> int list -> int list -> int list -> equality_bag 

(* given an equality, returns the numerical id *)
val id_of: equality -> int

(* profiling statistics *)
val get_stats: unit -> string


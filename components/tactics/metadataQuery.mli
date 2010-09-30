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
 * http://helm.cs.unibo.it/
 *)

  (** @param vars if set variables (".var" URIs) are considered. Defaults to
  * false
  * @param pat shell like pattern matching over object names, a string where "*"
  * is interpreted as 0 or more characters and "?" as exactly one character *)

(* used only by the old auto *)
val signature_of_goal:
  dbd:HSql.dbd -> ProofEngineTypes.status ->
    UriManager.uri list

val signature_of:
 Cic.metasenv -> 
  ProofEngineTypes.goal ->
  MetadataConstraints.UriManagerSet.t

val signature_of_hypothesis:
  Cic.hypothesis list -> 
  Cic.metasenv -> 
  MetadataConstraints.UriManagerSet.t

val close_with_types: 
  MetadataConstraints.UriManagerSet.t ->
  Cic.metasenv -> 
  Cic.context -> 
  MetadataConstraints.UriManagerSet.t

val universe_of_goal:
  dbd:HSql.dbd -> 
  bool ->  (* apply only or not *)
  Cic.metasenv -> 
  ProofEngineTypes.goal ->
    UriManager.uri list

val equations_for_goal:
  dbd:HSql.dbd -> 
  ?signature:MetadataConstraints.term_signature ->
    ProofEngineTypes.status -> UriManager.uri list

val experimental_hint:
  dbd:HSql.dbd ->
  ?facts:bool ->
  ?signature:MetadataConstraints.term_signature ->
  ProofEngineTypes.status ->
    (UriManager.uri * 
     ((Cic.term -> Cic.term) *
       (ProofEngineTypes.proof * ProofEngineTypes.goal list))) list

val new_experimental_hint:
  dbd:HSql.dbd ->
  ?facts:bool ->
  ?signature:MetadataConstraints.term_signature ->
  universe:UriManager.uri list ->
  ProofEngineTypes.status ->
    (UriManager.uri * 
     ((Cic.term -> Cic.term) *
       (ProofEngineTypes.proof * ProofEngineTypes.goal list))) list


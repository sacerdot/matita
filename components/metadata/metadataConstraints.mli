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

module UriManagerSet : Set.S with type elt = UriManager.uri
module SetSet: Set.S with type elt = UriManagerSet.t

  (** @return <main, constants>
  * main: constant in main position and, for polymorphic constants, type
  * instantitation
  * constants: constants appearing in term *)
type term_signature = (UriManager.uri * UriManager.uri list) option * UriManagerSet.t

(** {2 Candidates filtering} *)

  (** @return sorted list of theorem URIs, first URIs in the least have higher
  * relevance *)
val cmatch: dbd:HSql.dbd -> ?facts:bool -> Cic.term -> UriManager.uri list

  (** as cmatch, but returned list is not sorted but rather tagged with
  * relevance information: higher the tag, higher the relevance *)
val cmatch': dbd:HSql.dbd -> ?facts:bool -> Cic.term -> (int * UriManager.uri) list

type where = [ `Conclusion | `Statement ] (** signature matching extent *)

  (** @param where defaults to `Conclusion *)
val sigmatch:
  dbd:HSql.dbd ->
  ?facts:bool ->
  ?where:where -> 
  term_signature ->
    (int * UriManager.uri) list

(** {2 Constraint engine} *)

  (** constraing on the number of distinct constants *)
type cardinality_condition =
  | Eq of int
  | Gt of int
  | Lt of int

type rating_criterion =
  [ `Hits   (** order by number of hits, most used objects first *)
  ]

val add_constraint:
  ?start:int ->
  ?tables:string * string * string * string ->
  int * string list * string list ->
  MetadataTypes.constr ->
  int * string list * string list

  (** @param concl_card cardinality condition on conclusion only
  * @param full_card cardinality condition on the whole statement
  * @param diff required difference between the number of different constants in
  * hypothesis and the number of different constants in body
  * @return list of URI satisfying given constraints *)

val at_least:
  dbd:HSql.dbd ->
  ?concl_card:cardinality_condition ->
  ?full_card:cardinality_condition ->
  ?diff:cardinality_condition ->
  ?rating:rating_criterion ->
  MetadataTypes.constr list ->
    UriManager.uri list

  (** @param where defaults to `Conclusion *)
val at_most:
  dbd:HSql.dbd ->
  ?where:where -> UriManagerSet.t ->
    (UriManager.uri -> bool)

val add_all_constr: 
  ?tbl:string ->
   int * string list * string list ->
  cardinality_condition option ->
  cardinality_condition option ->
  cardinality_condition option ->
  int * string list * string list

val exec: 
  HSql.dbtype ->
  dbd:HSql.dbd ->
  ?rating:[ `Hits ] -> 
  int * string list * string list -> 
  UriManager.uri list

val signature_of: Cic.term -> term_signature
val constants_of: Cic.term -> UriManagerSet.t


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

  (** @return the one step direct dependencies of an object, specified by URI
   * (that is, the list of objects on which an given one depends) *)
val direct_deps:
  dbd:HSql.dbd ->
  UriManager.uri -> (UriManager.uri * MetadataTypes.position) list

  (** @return the one step inverse dependencies of an objects, specified by URI
   * (that is, the list of objects which depends on a given object) *)
val inverse_deps:
  dbd:HSql.dbd ->
  UriManager.uri -> (UriManager.uri * MetadataTypes.position) list

val topological_sort:
  dbd:HSql.dbd -> UriManager.uri list -> UriManager.uri list

val sorted_uris_of_baseuri:
   dbd:HSql.dbd -> string -> UriManager.uri list

  (** Representation of a (lazy) dependency graph.
   * Imperative data structure. *)
module DepGraph:
sig
  type t

  val dummy: t

  val expand: UriManager.uri -> t -> unit   (** ignores uri not found *)
  val collapse: UriManager.uri -> t -> unit (** ignores uri not found *)
  val render: Format.formatter -> t -> unit

    (** @return the transitive closure of direct_deps *)
  val direct_deps: dbd:HSql.dbd -> UriManager.uri -> t

    (** @return the transitive closure of inverse_deps *)
  val inverse_deps: dbd:HSql.dbd -> UriManager.uri -> t
end


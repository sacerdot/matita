(* Copyright (C) 2003-2005, HELM Team.
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

module S: Set.S with type elt = int

val overlaps: S.t -> S.t -> bool

val get_rels_from_premise: int -> Cic.term -> S.t

val get_mutinds_of_uri: UriManager.uri -> Cic.term -> S.t

(* count_nodes n t returns n + the number of nodes in t                *)
(* implicits, metas and casts are counted if ~meta:true                *)
(* if ~meta:false, complies with                                       *)
(* F.Guidi: Procedural representation of CIC Proof Terms. Last version *)
val count_nodes: meta:bool -> int -> Cic.term -> int

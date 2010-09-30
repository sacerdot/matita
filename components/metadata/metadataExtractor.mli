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

val compute: 
  body:Cic.term option -> 
  ty:Cic.term -> 
    MetadataTypes.metadata list

    (** @return tuples <uri, shortname, metadata> *)
val compute_obj:
  UriManager.uri -> 
    (UriManager.uri * string * MetadataTypes.metadata list) list
    
module IntSet: Set.S with type elt = int

  (** given a term, returns a pair of sets corresponding respectively to the set
    * of meta numbers occurring in term's conclusion and the set of meta numbers
    * occurring in term's hypotheses *)
val compute_metas: Cic.term -> IntSet.t * IntSet.t


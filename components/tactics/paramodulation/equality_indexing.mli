(* Copyright (C) 2005, HELM Team.
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

module type EqualityIndex =
  sig
    module PosEqSet : Set.S with type elt = Utils.pos * Equality.equality
    type t = Discrimination_tree.Make(Cic_indexable.CicIndexable)(PosEqSet).t
    val empty : t
    val retrieve_generalizations : t -> Cic.term -> PosEqSet.t
    val retrieve_unifiables : t -> Cic.term -> PosEqSet.t
    val init_index : unit -> unit
    val remove_index : t -> Equality.equality -> t
    val index : t -> Equality.equality -> t
    val in_index : t -> Equality.equality -> bool
    val iter : t -> (Cic_indexable.CicIndexable.constant_name Discrimination_tree.path -> PosEqSet.t -> unit) -> unit
  end

module DT : EqualityIndex
module PT : EqualityIndex


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
 * http://cs.unibo.it/helm/.
 *)

(* $Id$ *)

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

module DT = 
struct
    module OrderedPosEquality = struct
	type t = Utils.pos * Equality.equality
	let compare (p1,e1) (p2,e2) = 
	  let rc = Pervasives.compare p1 p2 in
	    if rc = 0 then Equality.compare e1 e2 else rc
      end

    module PosEqSet = Set.Make(OrderedPosEquality);;
    
    include Discrimination_tree.Make(Cic_indexable.CicIndexable)(PosEqSet)
    

    (* DISCRIMINATION TREES *)
    let init_index () = () ;;

    let remove_index tree equality = 
      let _, _, (_, l, r, ordering), _,_ = Equality.open_equality equality in
	match ordering with
	  | Utils.Gt -> remove_index tree l (Utils.Left, equality)
	  | Utils.Lt -> remove_index tree r (Utils.Right, equality)
	  | _ -> 
	      let tree = remove_index tree r (Utils.Right, equality) in
		remove_index tree l (Utils.Left, equality)

    let index tree equality = 
      let _, _, (_, l, r, ordering), _,_ = Equality.open_equality equality in
	match ordering with
	  | Utils.Gt -> index tree l (Utils.Left, equality)
	  | Utils.Lt -> index tree r (Utils.Right, equality)
	  | _ -> 
	      let tree = index tree r (Utils.Right, equality) in
		index tree l (Utils.Left, equality)
  

    let in_index tree equality = 
      let _, _, (_, l, r, ordering), _,_ = Equality.open_equality equality in
      let meta_convertibility (pos,equality') = 
	Equality.meta_convertibility_eq equality equality' 
      in
	in_index tree l meta_convertibility || in_index tree r meta_convertibility

  end

module PT = 
  struct
    module OrderedPosEquality = struct
	type t = Utils.pos * Equality.equality
	let compare (p1,e1) (p2,e2) = 
	  let rc = Pervasives.compare p1 p2 in
	    if rc = 0 then Equality.compare e1 e2 else rc
      end

    module PosEqSet = Set.Make(OrderedPosEquality);;
    
    include Discrimination_tree.Make(Cic_indexable.CicIndexable)(PosEqSet)
    

    (* DISCRIMINATION TREES *)
    let init_index () = () ;;

    let remove_index tree equality = 
      let _, _, (_, l, r, ordering), _,_ = Equality.open_equality equality in
	  match ordering with
	  | Utils.Gt -> remove_index tree l (Utils.Left, equality)
	  | Utils.Lt -> remove_index tree r (Utils.Right, equality)
	  | _ -> 
	      let tree = remove_index tree r (Utils.Right, equality) in
		remove_index tree l (Utils.Left, equality)

    let index tree equality = 
      let _, _, (_, l, r, ordering), _,_ = Equality.open_equality equality in
	match ordering with
	  | Utils.Gt -> index tree l (Utils.Left, equality)
	  | Utils.Lt -> index tree r (Utils.Right, equality)
	  | _ -> 
	      let tree = index tree r (Utils.Right, equality) in
		index tree l (Utils.Left, equality)
  

    let in_index tree equality = 
      let _, _, (_, l, r, ordering), _,_ = Equality.open_equality equality in
      let meta_convertibility (pos,equality') = 
	Equality.meta_convertibility_eq equality equality' 
      in
	in_index tree l meta_convertibility || in_index tree r meta_convertibility
end


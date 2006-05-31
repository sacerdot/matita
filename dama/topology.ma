(**************************************************************************)
(*       ___                                                              *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||         The HELM team.                                      *)
(*      ||A||         http://helm.cs.unibo.it                             *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU General Public License Version 2                  *)
(*                                                                        *)
(**************************************************************************)

set "baseuri" "cic:/matita/topology/".

include "sets.ma".

record is_topology X (A: set X) (O: set (set X)) : Prop  ≝
 { top_subset: ∀B. B ∈ O → B ⊆ A;
   top_empty: ∅︀ ∈ O;
   top_full: A ∈ O;
   top_intersection: ∀B,C. B ∈ O → C ∈ O → B ∩ C ∈ O;
   top_countable_union:
     ∀B.(∀i.(B \sub i) ∈ O) → (∪ \sub i (B \sub i)) ∈ O
 }.
 
record topological_space : Type ≝
 { top_carrier:> Type;
   top_domain:> set top_carrier;
   top_O: set (set top_carrier);
   top_is_topological_space:> is_topology ? top_domain top_O
 }.

(*definition is_continuous_map ≝
 λX,Y: topological_space.λf: X → Y.
  ∀V. V ∈ top_O Y → (f \sup -1) V ∈ top_O X.*)
definition is_continuous_map ≝
 λX,Y: topological_space.λf: X → Y.
  ∀V. V ∈ top_O Y → inverse_image ? ? f V ∈ top_O X.

record continuous_map (X,Y: topological_space) : Type ≝
 { cm_f:> X → Y;
   cm_is_continuous_map: is_continuous_map ? ? cm_f
 }.
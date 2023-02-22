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



include "classical_pointwise/topology.ma".

record is_sigma_algebra (X:Type) (A: set X) (M: set (set X)) : Prop ≝
 { siga_subset: ∀B.B ∈ M → B ⊆ A;
   siga_full: A ∈ M;
   siga_compl: ∀B.B ∈ M → B \sup c ∈ M;
   siga_enumerable_union:
    ∀B:seq (set X).(∀i.(B \sub i) ∈ M) → (∪ \sub i B \sub i) ∈ M
 }.

record sigma_algebra : Type ≝
 { siga_carrier:> Type;
   siga_domain:> set siga_carrier;
   M: set (set siga_carrier);
   siga_is_sigma_algebra:> is_sigma_algebra ? siga_domain M
 }.

(*definition is_measurable_map ≝
 λX:sigma_algebra.λY:topological_space.λf:X → Y.
  ∀V. V ∈ O Y → f \sup -1 V ∈ M X.*)
definition is_measurable_map ≝
 λX:sigma_algebra.λY:topological_space.λf:X → Y.
  ∀V. V ∈ O Y → inverse_image ? ? f V ∈ M X.


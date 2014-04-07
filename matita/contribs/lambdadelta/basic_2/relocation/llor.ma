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

include "basic_2/notation/relations/lazyor_4.ma".
include "basic_2/relocation/lpx_sn_alt.ma".

(* LAZY UNION FOR LOCAL ENVIRONMENTS ****************************************)

inductive clor (T) (L2) (K1) (V1): predicate term ≝
| clor_sn: ∀U. |K1| < |L2| → ⇧[|L2|-|K1|-1, 1] U ≡ T → clor T L2 K1 V1 V1
| clor_dx: ∀I,K2,V2. |K1| < |L2| → (∀U. ⇧[|L2|-|K1|-1, 1] U ≡ T → ⊥) →
           ⇩[|L2|-|K1|-1] L2 ≡ K2.ⓑ{I}V2 → clor T L2 K1 V1 V2
.

definition llor: relation4 term lenv lenv lenv ≝
                 λT,L2. lpx_sn (clor T L2).

interpretation
   "lazy union (local environment)"
   'LazyOr L1 T L2 L = (llor T L2 L1 L).

(* Basic properties *********************************************************)

lemma llor_pair_sn: ∀I,L1,L2,L,V,T,U. L1 ⩖[T] L2 ≡ L →
                    |L1| < |L2| → ⇧[|L2|-|L1|-1, 1] U ≡ T →
                    L1.ⓑ{I}V ⩖[T] L2 ≡ L.ⓑ{I}V.
/3 width=2 by clor_sn, lpx_sn_pair/ qed.

lemma llor_pair_dx: ∀I,J,L1,L2,L,K2,V1,V2,T. L1 ⩖[T] L2 ≡ L →
                    |L1| < |L2| → (∀U. ⇧[|L2|-|L1|-1, 1] U ≡ T → ⊥) →
                    ⇩[|L2|-|L1|-1] L2 ≡ K2.ⓑ{J}V2 →
                    L1.ⓑ{I}V1 ⩖[T] L2 ≡ L.ⓑ{I}V2.
/4 width=3 by clor_dx, lpx_sn_pair/ qed.

lemma llor_total: ∀T,L2,L1. |L1| ≤ |L2| → ∃L. L1 ⩖[T] L2 ≡ L.
#T #L2 #L1 elim L1 -L1 /2 width=2 by ex_intro/
#L1 #I1 #V1 #IHL1 normalize
#H elim IHL1 -IHL1 /2 width=3 by transitive_le/
#L #HT elim (is_lift_dec T (|L2|-|L1|-1) 1)
[ * /3 width=2 by llor_pair_sn, ex_intro/
| elim (ldrop_O1_lt L2 (|L2|-|L1|-1))
  /5 width=4 by llor_pair_dx, monotonic_lt_minus_l, ex_intro/
]
qed-.

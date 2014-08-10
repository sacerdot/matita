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

include "basic_2/substitution/lift_lift.ma".
include "basic_2/multiple/mr2_minus.ma".
include "basic_2/multiple/lifts.ma".

(* GENERIC TERM RELOCATION **************************************************)

(* Properties concerning basic term relocation ******************************)

(* Basic_1: was: lift1_xhg (right to left) *)
lemma lifts_lift_trans_le: ∀T1,T,des. ⇧*[des] T1 ≡ T → ∀T2. ⇧[0, 1] T ≡ T2 →
                           ∃∃T0. ⇧[0, 1] T1 ≡ T0 & ⇧*[des + 1] T0 ≡ T2.
#T1 #T #des #H elim H -T1 -T -des
[ /2 width=3/
| #T1 #T3 #T #des #d #e #HT13 #_ #IHT13 #T2 #HT2
  elim (IHT13 … HT2) -T #T #HT3 #HT2
  elim (lift_trans_le … HT13 … HT3) -T3 // /3 width=5/
]
qed-.

(* Basic_1: was: lift1_free (right to left) *)
lemma lifts_lift_trans: ∀des,i,i0. @⦃i, des⦄ ≡ i0 →
                        ∀des0. des + 1 ▭ i + 1 ≡ des0 + 1 →
                        ∀T1,T0. ⇧*[des0] T1 ≡ T0 →
                        ∀T2. ⇧[O, i0 + 1] T0 ≡ T2 →
                        ∃∃T. ⇧[0, i + 1] T1 ≡ T & ⇧*[des] T ≡ T2.
#des elim des -des normalize
[ #i #x #H1 #des0 #H2 #T1 #T0 #HT10 #T2
  <(at_inv_nil … H1) -x #HT02
  lapply (minuss_inv_nil1 … H2) -H2 #H
  >(pluss_inv_nil2 … H) in HT10; -des0 #H
  >(lifts_inv_nil … H) -T1 /2 width=3/
| #d #e #des #IHdes #i #i0 #H1 #des0 #H2 #T1 #T0 #HT10 #T2 #HT02
  elim (at_inv_cons … H1) -H1 * #Hid #Hi0
  [ elim (minuss_inv_cons1_lt … H2) -H2 [2: /2 width=1/ ] #des1 #Hdes1 <minus_le_minus_minus_comm // <minus_plus_m_m #H
    elim (pluss_inv_cons2 … H) -H #des2 #H1 #H2 destruct
    elim (lifts_inv_cons … HT10) -HT10 #T >minus_plus #HT1 #HT0
    elim (IHdes … Hi0 … Hdes1 … HT0 … HT02) -IHdes -Hi0 -Hdes1 -T0 #T0 #HT0 #HT02
    elim (lift_trans_le … HT1 … HT0) -T /2 width=1/ #T #HT1 <plus_minus_m_m /2 width=1/ /3 width=5/
  | >commutative_plus in Hi0; #Hi0
    lapply (minuss_inv_cons1_ge … H2 ?) -H2 [ /2 width=1/ ] <associative_plus #Hdes0
    elim (IHdes … Hi0 … Hdes0 … HT10 … HT02) -IHdes -Hi0 -Hdes0 -T0 #T0 #HT0 #HT02
    elim (lift_split … HT0 d (i+1)) -HT0 /2 width=1/ /3 width=5/
  ]
]
qed-.

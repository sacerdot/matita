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

include "basic_2A/substitution/lift_lift.ma".
include "basic_2A/multiple/mr2_minus.ma".
include "basic_2A/multiple/lifts.ma".

(* GENERIC TERM RELOCATION **************************************************)

(* Properties concerning basic term relocation ******************************)

(* Basic_1: was: lift1_xhg (right to left) *)
lemma lifts_lift_trans_le: ∀T1,T,cs. ⬆*[cs] T1 ≡ T → ∀T2. ⬆[0, 1] T ≡ T2 →
                           ∃∃T0. ⬆[0, 1] T1 ≡ T0 & ⬆*[cs + 1] T0 ≡ T2.
#T1 #T #cs #H elim H -T1 -T -cs
[ /2 width=3 by lifts_nil, ex2_intro/
| #T1 #T3 #T #cs #l #m #HT13 #_ #IHT13 #T2 #HT2
  elim (IHT13 … HT2) -T #T #HT3 #HT2
  elim (lift_trans_le … HT13 … HT3) -T3 /3 width=5 by lifts_cons, ex2_intro/
]
qed-.

(* Basic_1: was: lift1_free (right to left) *)
lemma lifts_lift_trans: ∀cs,i,i0. @⦃i, cs⦄ ≡ i0 →
                        ∀cs0. cs + 1 ▭ i + 1 ≡ cs0 + 1 →
                        ∀T1,T0. ⬆*[cs0] T1 ≡ T0 →
                        ∀T2. ⬆[O, i0 + 1] T0 ≡ T2 →
                        ∃∃T. ⬆[0, i + 1] T1 ≡ T & ⬆*[cs] T ≡ T2.
#cs elim cs -cs normalize
[ #i #x #H1 #cs0 #H2 #T1 #T0 #HT10 #T2
  <(at_inv_nil … H1) -x #HT02
  lapply (minuss_inv_nil1 … H2) -H2 #H
  >(pluss_inv_nil2 … H) in HT10; -cs0 #H
  >(lifts_inv_nil … H) -T1 /2 width=3 by lifts_nil, ex2_intro/
| #l #m #cs #IHcs #i #i0 #H1 #cs0 #H2 #T1 #T0 #HT10 #T2 #HT02
  elim (at_inv_cons … H1) -H1 * #Hil #Hi0
  [ elim (minuss_inv_cons1_lt … H2) -H2 [2: /2 width=1 by lt_minus_to_plus/ ] #cs1 #Hcs1 <minus_le_minus_minus_comm // <minus_plus_m_m #H
    elim (pluss_inv_cons2 … H) -H #cs2 #H1 #H2 destruct
    elim (lifts_inv_cons … HT10) -HT10 #T >minus_plus #HT1 #HT0
    elim (IHcs … Hi0 … Hcs1 … HT0 … HT02) -IHcs -Hi0 -Hcs1 -T0 #T0 #HT0 #HT02
    elim (lift_trans_le … HT1 … HT0) -T /2 width=1 by/ #T #HT1 <plus_minus_m_m /3 width=5 by lifts_cons, ex2_intro/
  | >commutative_plus in Hi0; #Hi0
    lapply (minuss_inv_cons1_ge … H2 ?) -H2 [ /2 width=1 by le_S_S/ ] <associative_plus #Hcs0
    elim (IHcs … Hi0 … Hcs0 … HT10 … HT02) -IHcs -Hi0 -Hcs0 -T0 #T0 #HT0 #HT02
    elim (lift_split … HT0 l (i+1)) -HT0 /3 width=5 by lifts_cons, le_S, ex2_intro/
  ]
]
qed-.

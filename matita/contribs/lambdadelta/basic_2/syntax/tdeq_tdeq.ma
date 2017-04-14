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

include "basic_2/syntax/tdeq.ma".

(* DEGREE-BASED EQUIVALENCE ON TERMS ****************************************)

(* Main properties **********************************************************)

theorem tdeq_trans: ∀h,o. Transitive … (tdeq h o).
#h #o #T1 #T #H elim H -T1 -T
[ #s1 #s #d #Hs1 #Hs #X #H
  elim (tdeq_inv_sort1_deg … H … Hs) -s /2 width=3 by tdeq_sort/
| #i1 #i #H <(tdeq_inv_lref1 … H) -H //
| #l1 #l #H <(tdeq_inv_gref1 … H) -H //
| #I #V1 #V #T1 #T #_ #_ #IHV #IHT #X #H
  elim (tdeq_inv_pair1 … H) -H /3 width=1 by tdeq_pair/
]
qed-.

theorem tdeq_canc_sn: ∀h,o. left_cancellable … (tdeq h o).
/3 width=3 by tdeq_trans, tdeq_sym/ qed-.

theorem tdeq_canc_dx: ∀h,o. right_cancellable … (tdeq h o).
/3 width=3 by tdeq_trans, tdeq_sym/ qed-.

theorem tdeq_repl: ∀h,o,T1,T2. T1 ≡[h, o] T2 →
                   ∀U1. T1 ≡[h, o] U1 → ∀U2. T2 ≡[h, o] U2 → U1 ≡[h, o] U2.
/3 width=3 by tdeq_canc_sn, tdeq_trans/ qed-.

(* Negated main properies ***************************************************)

theorem tdeq_tdneq_trans: ∀h,o,T1,T. T1 ≡[h, o] T → ∀T2. (T ≡[h, o] T2 → ⊥) →
                          T1 ≡[h, o] T2 → ⊥.
/3 width=3 by tdeq_canc_sn/ qed-.

theorem tdneq_tdeq_canc_dx: ∀h,o,T1,T. (T1 ≡[h, o] T → ⊥) → ∀T2. T2 ≡[h, o] T →
                            T1 ≡[h, o] T2 → ⊥.
/3 width=3 by tdeq_trans/ qed-.

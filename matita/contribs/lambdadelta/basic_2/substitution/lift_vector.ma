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

include "basic_2/grammar/term_vector.ma".
include "basic_2/substitution/lift.ma".

(* BASIC TERM VECTOR RELOCATION *********************************************)

inductive liftv (l,m:nat) : relation (list term) ≝
| liftv_nil : liftv l m (◊) (◊)
| liftv_cons: ∀T1s,T2s,T1,T2.
              ⬆[l, m] T1 ≡ T2 → liftv l m T1s T2s →
              liftv l m (T1 @ T1s) (T2 @ T2s)
.

interpretation "relocation (vector)" 'RLift l m T1s T2s = (liftv l m T1s T2s).

(* Basic inversion lemmas ***************************************************)

fact liftv_inv_nil1_aux: ∀T1s,T2s,l,m. ⬆[l, m] T1s ≡ T2s → T1s = ◊ → T2s = ◊.
#T1s #T2s #l #m * -T1s -T2s //
#T1s #T2s #T1 #T2 #_ #_ #H destruct
qed-.

lemma liftv_inv_nil1: ∀T2s,l,m. ⬆[l, m] ◊ ≡ T2s → T2s = ◊.
/2 width=5 by liftv_inv_nil1_aux/ qed-.

fact liftv_inv_cons1_aux: ∀T1s,T2s,l,m. ⬆[l, m] T1s ≡ T2s →
                          ∀U1,U1s. T1s = U1 @ U1s →
                          ∃∃U2,U2s. ⬆[l, m] U1 ≡ U2 & ⬆[l, m] U1s ≡ U2s &
                                    T2s = U2 @ U2s.
#T1s #T2s #l #m * -T1s -T2s
[ #U1 #U1s #H destruct
| #T1s #T2s #T1 #T2 #HT12 #HT12s #U1 #U1s #H destruct /2 width=5 by ex3_2_intro/
]
qed-.

lemma liftv_inv_cons1: ∀U1,U1s,T2s,l,m. ⬆[l, m] U1 @ U1s ≡ T2s →
                       ∃∃U2,U2s. ⬆[l, m] U1 ≡ U2 & ⬆[l, m] U1s ≡ U2s &
                                 T2s = U2 @ U2s.
/2 width=3 by liftv_inv_cons1_aux/ qed-.

(* Basic properties *********************************************************)

lemma liftv_total: ∀l,m. ∀T1s:list term. ∃T2s. ⬆[l, m] T1s ≡ T2s.
#l #m #T1s elim T1s -T1s
[ /2 width=2 by liftv_nil, ex_intro/
| #T1 #T1s * #T2s #HT12s
  elim (lift_total T1 l m) /3 width=2 by liftv_cons, ex_intro/
]
qed-.

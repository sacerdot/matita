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

inductive liftv (d,e:nat) : relation (list term) ≝
| liftv_nil : liftv d e (◊) (◊)
| liftv_cons: ∀T1s,T2s,T1,T2.
              ⇧[d, e] T1 ≡ T2 → liftv d e T1s T2s →
              liftv d e (T1 @ T1s) (T2 @ T2s)
.

interpretation "relocation (vector)" 'RLift d e T1s T2s = (liftv d e T1s T2s).

(* Basic inversion lemmas ***************************************************)

fact liftv_inv_nil1_aux: ∀T1s,T2s,d,e. ⇧[d, e] T1s ≡ T2s → T1s = ◊ → T2s = ◊.
#T1s #T2s #d #e * -T1s -T2s //
#T1s #T2s #T1 #T2 #_ #_ #H destruct
qed-.

lemma liftv_inv_nil1: ∀T2s,d,e. ⇧[d, e] ◊ ≡ T2s → T2s = ◊.
/2 width=5 by liftv_inv_nil1_aux/ qed-.

fact liftv_inv_cons1_aux: ∀T1s,T2s,d,e. ⇧[d, e] T1s ≡ T2s →
                          ∀U1,U1s. T1s = U1 @ U1s →
                          ∃∃U2,U2s. ⇧[d, e] U1 ≡ U2 & ⇧[d, e] U1s ≡ U2s &
                                    T2s = U2 @ U2s.
#T1s #T2s #d #e * -T1s -T2s
[ #U1 #U1s #H destruct
| #T1s #T2s #T1 #T2 #HT12 #HT12s #U1 #U1s #H destruct /2 width=5 by ex3_2_intro/
]
qed-.

lemma liftv_inv_cons1: ∀U1,U1s,T2s,d,e. ⇧[d, e] U1 @ U1s ≡ T2s →
                       ∃∃U2,U2s. ⇧[d, e] U1 ≡ U2 & ⇧[d, e] U1s ≡ U2s &
                                 T2s = U2 @ U2s.
/2 width=3 by liftv_inv_cons1_aux/ qed-.

(* Basic properties *********************************************************)

lemma liftv_total: ∀d,e. ∀T1s:list term. ∃T2s. ⇧[d, e] T1s ≡ T2s.
#d #e #T1s elim T1s -T1s
[ /2 width=2 by liftv_nil, ex_intro/
| #T1 #T1s * #T2s #HT12s
  elim (lift_total T1 d e) /3 width=2 by liftv_cons, ex_intro/
]
qed-.

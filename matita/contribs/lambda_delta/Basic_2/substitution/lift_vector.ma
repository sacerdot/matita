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

include "Basic_2/grammar/term_vector.ma".
include "Basic_2/substitution/lift.ma".

(* RELOCATION ***************************************************************)

inductive liftv (d,e:nat) : relation (list term) ≝
| liftv_nil : liftv d e ◊ ◊
| liftv_cons: ∀T1s,T2s,T1,T2.
              ⇧[d, e] T1 ≡ T2 → liftv d e T1s T2s →
              liftv d e (T1 :: T1s) (T2 :: T2s)
.

interpretation "relocation (vector)" 'RLift d e T1s T2s = (liftv d e T1s T2s).

(* Basic properties *********************************************************)

lemma liftv_total: ∀d,e. ∀T1s:list term. ∃T2s. ⇧[d, e] T1s ≡ T2s.
#d #e #T1s elim T1s -T1s
[ /2 width=2/
| #T1 #T1s * #T2s #HT12s
  elim (lift_total T1 d e) /3 width=2/
]
qed-.

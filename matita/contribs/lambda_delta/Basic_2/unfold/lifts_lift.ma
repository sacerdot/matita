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

include "Basic_2/substitution/lift_lift.ma".
include "Basic_2/unfold/lifts.ma".

(* GENERIC TERM RELOCATION **************************************************)

(* Properties concerning basic term relocation ******************************)

(* Basic_1: was: lift1_xhg *)
lemma lifts_lift_trans_le: ∀T1,T,des. ⇧*[des] T1 ≡ T → ∀T2. ⇧[0, 1] T ≡ T2 →
                           ∃∃T0. ⇧[0, 1] T1 ≡ T0 & ⇧*[des + 1] T0 ≡ T2.
#T1 #T #des #H elim H -T1 -T -des
[ /2 width=3/
| #T1 #T3 #T #des #d #e #HT13 #_ #IHT13 #T2 #HT2
  elim (IHT13 … HT2) -T #T #HT3 #HT2
  elim (lift_trans_le … HT13 … HT3 ?) -T3 // /3 width=5/
]
qed-.

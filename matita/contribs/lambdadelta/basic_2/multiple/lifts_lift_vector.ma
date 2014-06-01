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

include "basic_2/substitution/lift_lift_vector.ma".
include "basic_2/multiple/lifts_lift.ma".
include "basic_2/multiple/lifts_vector.ma".

(* GENERIC RELOCATION *******************************************************)

(* Main properties **********************************************************)

(* Basic_1: was: lifts1_xhg (right to left) *)
lemma liftsv_liftv_trans_le: ∀T1s,Ts,des. ⇧*[des] T1s ≡ Ts →
                             ∀T2s:list term. ⇧[0, 1] Ts ≡ T2s →
                             ∃∃T0s. ⇧[0, 1] T1s ≡ T0s & ⇧*[des + 1] T0s ≡ T2s.
#T1s #Ts #des #H elim H -T1s -Ts
[ #T1s #H
  >(liftv_inv_nil1 … H) -T1s /2 width=3/
| #T1s #Ts #T1 #T #HT1 #_ #IHT1s #X #H
  elim (liftv_inv_cons1 … H) -H #T2 #T2s #HT2 #HT2s #H destruct
  elim (IHT1s … HT2s) -Ts #Ts #HT1s #HT2s
  elim (lifts_lift_trans_le … HT1 … HT2) -T /3 width=5/
]
qed-.

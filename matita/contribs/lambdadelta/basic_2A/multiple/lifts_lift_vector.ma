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

include "basic_2A/substitution/lift_lift_vector.ma".
include "basic_2A/multiple/lifts_lift.ma".
include "basic_2A/multiple/lifts_vector.ma".

(* GENERIC RELOCATION *******************************************************)

(* Main properties **********************************************************)

(* Basic_1: was: lifts1_xhg (right to left) *)
lemma liftsv_liftv_trans_le: ∀T1s,Ts,cs. ⬆*[cs] T1s ≡ Ts →
                             ∀T2s:list term. ⬆[0, 1] Ts ≡ T2s →
                             ∃∃T0s. ⬆[0, 1] T1s ≡ T0s & ⬆*[cs + 1] T0s ≡ T2s.
#T1s #Ts #cs #H elim H -T1s -Ts
[ #T1s #H
  >(liftv_inv_nil1 … H) -T1s /2 width=3 by liftsv_nil, liftv_nil, ex2_intro/
| #T1s #Ts #T1 #T #HT1 #_ #IHT1s #X #H
  elim (liftv_inv_cons1 … H) -H #T2 #T2s #HT2 #HT2s #H destruct
  elim (IHT1s … HT2s) -Ts #Ts #HT1s #HT2s
  elim (lifts_lift_trans_le … HT1 … HT2) -T /3 width=5 by liftsv_cons, liftv_cons, ex2_intro/
]
qed-.

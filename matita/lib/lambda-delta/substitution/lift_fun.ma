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

include "lambda-delta/substitution/lift_defs.ma".

(* RELOCATION ***************************************************************)

(* Functional properties ****************************************************)

lemma lift_total: ∀T1,d,e. ∃T2. ↑[d,e] T1 ≡ T2.
#T1 elim T1 -T1
[ /2/
| #i #d #e elim (lt_or_ge i d) /3/
| * #I #V1 #T1 #IHV1 #IHT1 #d #e
  elim (IHV1 d e) -IHV1 #V2 #HV12
  [ elim (IHT1 (d+1) e) -IHT1 /3/
  | elim (IHT1 d e) -IHT1 /3/
  ]
]
qed.

lemma lift_mono:  ∀d,e,T,U1. ↑[d,e] T ≡ U1 → ∀U2. ↑[d,e] T ≡ U2 → U1 = U2.
#d #e #T #U1 #H elim H -H d e T U1
[ #k #d #e #X #HX
  lapply (lift_inv_sort1 … HX) -HX //
| #i #d #e #Hid #X #HX 
  lapply (lift_inv_lref1_lt … HX ?) -HX //
| #i #d #e #Hdi #X #HX 
  lapply (lift_inv_lref1_ge … HX ?) -HX //
| #I #V1 #V2 #T1 #T2 #d #e #_ #_ #IHV12 #IHT12 #X #HX
  elim (lift_inv_bind1 … HX) -HX #V #T #HV1 #HT1 #HX destruct -X /3/
| #I #V1 #V2 #T1 #T2 #d #e #_ #_ #IHV12 #IHT12 #X #HX
  elim (lift_inv_flat1 … HX) -HX #V #T #HV1 #HT1 #HX destruct -X /3/
]
qed.

lemma lift_inj:  ∀d,e,T1,U. ↑[d,e] T1 ≡ U → ∀T2. ↑[d,e] T2 ≡ U → T1 = T2.
#d #e #T1 #U #H elim H -H d e T1 U
[ #k #d #e #X #HX
  lapply (lift_inv_sort2 … HX) -HX //
| #i #d #e #Hid #X #HX 
  lapply (lift_inv_lref2_lt … HX ?) -HX //
| #i #d #e #Hdi #X #HX 
  lapply (lift_inv_lref2_ge … HX ?) -HX /2/
| #I #V1 #V2 #T1 #T2 #d #e #_ #_ #IHV12 #IHT12 #X #HX
  elim (lift_inv_bind2 … HX) -HX #V #T #HV1 #HT1 #HX destruct -X /3/
| #I #V1 #V2 #T1 #T2 #d #e #_ #_ #IHV12 #IHT12 #X #HX
  elim (lift_inv_flat2 … HX) -HX #V #T #HV1 #HT1 #HX destruct -X /3/
]
qed.

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

include "lambda-delta/substitution/lift_main.ma".
include "lambda-delta/substitution/subst_defs.ma".
include "lambda-delta/reduction/pr_defs.ma".

lemma subst_pr: ∀d,e,L,T1,U2. L ⊢ ↓[d,e] T1 ≡ U2 → ∀T2. ↑[d,e] U2 ≡ T2 →
                L ⊢ T1 ⇒ T2.
#d #e #L #T1 #U2 #H elim H -H d e L T1 U2
[ #L #k #d #e #X #HX
  lapply (lift_inv_sort1 … HX) -HX #HX destruct -X //
| #L #i #d #e #Hid #X #HX
  lapply (lift_inv_lref1_lt … HX Hid) -HX #HX destruct -X //
| #L #K #V #U1 #U2 #i #d #e #Hdi #Hide #HLK #_ #HU12 #IHVU1 #U #HU2
  lapply (lift_trans_be … HU12 … HU2 ? ?) // -HU12 HU2 U2 #HU1
  elim (lift_free … HU1 0 (d+e-i-1) ? ? ?) -HU1 // #U2 #HU12 >arith6 // #HU2
  @pr_delta [4,5,6: /2/ |1,2,3: skip ] (**) (* /2/ *)
| #L #i #d #e #Hdei #X #HX
  lapply (lift_inv_lref1_ge … HX ?) -HX /2/ #HX destruct -X;
  >arith7 /2/
| #L #I #V1 #V2 #T1 #T2 #d #e #_ #_ #IHV12 #IHT12 #X #HX
  elim (lift_inv_bind1 … HX) -HX #V #T #HV2 #HT2 #HX destruct -X /3/
| #L #I #V1 #V2 #T1 #T2 #d #e #_ #_ #IHV12 #IHT12 #X #HX
  elim (lift_inv_flat1 … HX) -HX #V #T #HV2 #HT2 #HX destruct -X /3/
]
qed.
(*
lemma pr_subst_pr: ∀L,T1,T. L ⊢ T1 ⇒ T → ∀d,e,U. L ⊢ ↓[d,e] T ≡ U →
                   ∀T2. ↑[d,e] U ≡ T2 → L ⊢ T1 ⇒ T2.
#L #T1 #T #H elim H -H L T1 T
[ /2 width=5/
| /2 width=5/
| #L #I #V1 #V2 #T1 #T2 #HV12 #HT12 #IHV12 #IHT12 #d #e #X2 #HX2 #X1 #HX1 
  elim (subst_inv_bind1 … HX2) -HX2 #V3 #T3 #HV23 #HT23 #H destruct -X2;
  elim (lift_inv_bind1 … HX1) -HX1 #V4 #T4 #HV34 #HT34 #H destruct -X1;
  @pr_bind /2 width=5/ @IHT12 
| #L #I #V1 #V2 #T1 #T2 #_ #_ #IHV12 #IHT12 #d #e #X2 #HX2 #X1 #HX1 
  elim (subst_inv_flat1 … HX2) -HX2 #V3 #T3 #HV23 #HT23 #H destruct -X2;
  elim (lift_inv_flat1 … HX1) -HX1 #V4 #T4 #HV34 #HT34 #H destruct -X1;
  /3 width=5/
| #L #V1 #V2 #W #T1 #T2 #_ #_ #IHV12 #IHT12 #d #e #X2 #HX2 #X1 #HX1
  elim (subst_inv_bind1 … HX2) -HX2 #V3 #T3 #HV23 #HT23 #H destruct -X2;
  elim (lift_inv_bind1 … HX1) -HX1 #V4 #T4 #HV34 #HT34 #H destruct -X1;
  @pr_beta /2 width=5/ @IHT12
| #L #K #V1 #V2 #V #i #HLK #HV12 #HV2 #IHV12 #d #e #U #HVU #U0 #HU0
  lapply (lift_free … HU0 0 (i + 1 + e) ? ? ?) // 
  
  
  @pr_delta [4: // |1,2: skip |6: 
*) 

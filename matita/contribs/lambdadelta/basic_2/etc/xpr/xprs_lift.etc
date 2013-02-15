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

include "basic_2/reducibility/xpr_lift.ma".
include "basic_2/computation/cprs.ma".
include "basic_2/computation/xprs.ma".

(* EXTENDED PARALLEL COMPUTATION ON TERMS ***********************************)

(* Advanced forward lemmas **************************************************)

lemma xprs_fwd_abst1: ∀h,g,a,L,V1,T1,U2. ⦃h, L⦄ ⊢ ⓛ{a}V1. T1 •➡*[g] U2 →
                      ∃∃V2,T2. L ⊢ V1 ➡* V2 & U2 = ⓛ{a}V2. T2.
#h #g #a #L #V1 #T1 #U2 #H @(xprs_ind … H) -U2 /2 width=4/
#U #U2 #_ #HU2 * #V #T #HV1 #H destruct
elim (xpr_inv_abst1 … HU2) -HU2 #V2 #T2 #HV2 #_ #H destruct /3 width=4/
qed-.

(* Relocation properties ****************************************************)

lemma xprs_lift: ∀L,K,d,e. ⇩[d, e] L ≡ K → ∀T1,U1. ⇧[d, e] T1 ≡ U1 →
                 ∀h,g,T2. ⦃h, K⦄ ⊢ T1 •➡*[g] T2 → ∀U2. ⇧[d, e] T2 ≡ U2 →
                 ⦃h, L⦄ ⊢ U1 •➡*[g] U2.
#L #K #d #e #HLK #T1 #U1 #HTU1 #h #g #T2 #HT12 @(xprs_ind … HT12) -T2
[ -HLK #T2 #HT12
   <(lift_mono … HTU1 … HT12) -T1 //
| -HTU1 #T #T2 #_ #HT2 #IHT2 #U2 #HTU2
  elim (lift_total T d e) #U #HTU
  lapply (xpr_lift … HLK … HTU … HTU2 … HT2) -T2 -HLK /3 width=3/
]
qed.

lemma xprs_inv_lift1: ∀L,K,d,e. ⇩[d, e] L ≡ K →
                      ∀T1,U1. ⇧[d, e] T1 ≡ U1 → ∀h,g,U2. ⦃h, L⦄ ⊢ U1 •➡*[g] U2 →
                      ∃∃T2. ⇧[d, e] T2 ≡ U2 & ⦃h, K⦄ ⊢ T1 •➡*[g] T2.
#L #K #d #e #HLK #T1 #U1 #HTU1 #h #g #U2 #HU12 @(xprs_ind … HU12) -U2 /2 width=3/
-HTU1 #U #U2 #_ #HU2 * #T #HTU #HT1
elim (xpr_inv_lift1 … HLK … HTU … HU2) -U -HLK /3 width=5/
qed.

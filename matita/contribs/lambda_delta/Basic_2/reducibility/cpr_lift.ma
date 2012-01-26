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

include "Basic_2/unfold/tpss_lift.ma".
include "Basic_2/reducibility/tpr_lift.ma".
include "Basic_2/reducibility/cpr.ma".

(* CONTEXT-SENSITIVE PARALLEL REDUCTION ON TERMS ****************************)

(* Advanced properties ******************************************************)

lemma cpr_cdelta: ∀L,K,V1,W1,W2,i.
                  ⇩[0, i] L ≡ K. ⓓV1 → K ⊢ V1 [0, |L| - i - 1] ▶* W1 →
                  ⇧[0, i + 1] W1 ≡ W2 → L ⊢ #i ➡ W2.
#L #K #V1 #W1 #W2 #i #HLK #HVW1 #HW12
lapply (ldrop_fwd_ldrop2_length … HLK) #Hi
@ex2_1_intro [2: // | skip | @tpss_subst /width=6/ ] (**) (* /3 width=6/ is too slow *)
qed.

(* Advanced inversion lemmas ************************************************)

(* Basic_1: was: pr2_gen_lref *)
lemma cpr_inv_lref1: ∀L,T2,i. L ⊢ #i ➡ T2 →
                     T2 = #i ∨
                     ∃∃K,V1,T1. ⇩[0, i] L ≡ K. ⓓV1 &
                                K ⊢ V1 [0, |L| - i - 1] ▶* T1 &
                                ⇧[0, i + 1] T1 ≡ T2 &
                                i < |L|.
#L #T2 #i * #X #H
>(tpr_inv_atom1 … H) -H #H
elim (tpss_inv_lref1 … H) -H /2 width=1/
* /3 width=6/
qed-.

(* Basic_1: was: pr2_gen_abst *)
lemma cpr_inv_abst1: ∀V1,T1,U2. ⓛV1. T1 ➡ U2 →
                     ∃∃V2,T2. V1 ➡ V2 & T1 ➡ T2 & U2 = ⓛV2. T2.
/2 width=3/ qed-.

(* Relocation properties ****************************************************)

(* Basic_1: was: pr2_lift *)
lemma cpr_lift: ∀L,K,d,e. ⇩[d, e] L ≡ K →
                ∀T1,U1. ⇧[d, e] T1 ≡ U1 → ∀T2,U2. ⇧[d, e] T2 ≡ U2 →
                K ⊢ T1 ➡ T2 → L ⊢ U1 ➡ U2.
#L #K #d #e #HLK #T1 #U1 #HTU1 #T2 #U2 #HTU2 * #T #HT1 #HT2
elim (lift_total T d e) #U #HTU 
lapply (tpr_lift … HT1 … HTU1 … HTU) -T1 #HU1
elim (lt_or_ge (|K|) d) #HKd
[ lapply (tpss_lift_le … HT2 … HLK HTU … HTU2) -T2 -T -HLK [ /2 width=2/ | /3 width=4/ ]
| lapply (tpss_lift_be … HT2 … HLK HTU … HTU2) -T2 -T -HLK // /3 width=4/
]
qed.

(* Basic_1: was: pr2_gen_lift *)
lemma cpr_inv_lift: ∀L,K,d,e. ⇩[d, e] L ≡ K →
                    ∀T1,U1. ⇧[d, e] T1 ≡ U1 → ∀U2. L ⊢ U1 ➡ U2 →
                    ∃∃T2. ⇧[d, e] T2 ≡ U2 & K ⊢ T1 ➡ T2.
#L #K #d #e #HLK #T1 #U1 #HTU1 #U2 * #U #HU1 #HU2
elim (tpr_inv_lift … HU1 … HTU1) -U1 #T #HTU #T1
elim (lt_or_ge (|L|) d) #HLd
[ elim (tpss_inv_lift1_le … HU2 … HLK … HTU ?) -U -HLK [ /5 width=4/ | /2 width=2/ ]
| elim (lt_or_ge (|L|) (d + e)) #HLde
  [ elim (tpss_inv_lift1_be_up … HU2 … HLK … HTU ? ?) -U -HLK // [ /5 width=4/ | /2 width=2/ ] 
  | elim (tpss_inv_lift1_be … HU2 … HLK … HTU ? ?) -U -HLK // /5 width=4/
  ]
]
qed.

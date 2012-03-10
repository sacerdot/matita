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

include "basic_2/reducibility/cpr_lift.ma".
include "basic_2/computation/cprs.ma".

(* CONTEXT-SENSITIVE PARALLEL COMPUTATION ON TERMS **************************)

(* Advanced inversion lemmas ************************************************)

(* Basic_1: was: pr3_gen_abst *)
lemma cprs_inv_abst1: ∀I,W,L,V1,T1,U2. L ⊢ ⓛV1. T1 ➡* U2 →
                      ∃∃V2,T2. L ⊢ V1 ➡* V2 & L. ⓑ{I} W ⊢ T1 ➡* T2 &
                               U2 = ⓛV2. T2.
#I #W #L #V1 #T1 #U2 #H @(cprs_ind … H) -U2 /2 width=5/
#U #U2 #_ #HU2 * #V #T #HV1 #HT1 #H destruct
elim (cpr_inv_abst1 … HU2 I W) -HU2 #V2 #T2 #HV2 #HT2 #H destruct  /3 width=5/
qed-.

(* Relocation properties ****************************************************)

(* Basic_1: was: pr3_lift *)
lemma cprs_lift: ∀L,K,d,e. ⇩[d, e] L ≡ K → ∀T1,U1. ⇧[d, e] T1 ≡ U1 →
                 ∀T2. K ⊢ T1 ➡* T2 → ∀U2. ⇧[d, e] T2 ≡ U2 →
                 L ⊢ U1 ➡* U2.
#L #K #d #e #HLK #T1 #U1 #HTU1 #T2 #HT12 @(cprs_ind … HT12) -T2
[ -HLK #T2 #HT12
   <(lift_mono … HTU1 … HT12) -T1 //
| -HTU1 #T #T2 #_ #HT2 #IHT2 #U2 #HTU2
  elim (lift_total T d e) #U #HTU
  lapply (cpr_lift … HLK … HTU … HTU2 … HT2) -T2 -HLK /3 width=3/
]
qed.

(* Basic_1: was: pr3_gen_lift *)
lemma cprs_inv_lift: ∀L,K,d,e. ⇩[d, e] L ≡ K →
                     ∀T1,U1. ⇧[d, e] T1 ≡ U1 → ∀U2. L ⊢ U1 ➡* U2 →
                     ∃∃T2. ⇧[d, e] T2 ≡ U2 & K ⊢ T1 ➡* T2.
#L #K #d #e #HLK #T1 #U1 #HTU1 #U2 #HU12 @(cprs_ind … HU12) -U2 /2 width=3/
-HTU1 #U #U2 #_ #HU2 * #T #HTU #HT1
elim (cpr_inv_lift … HLK … HTU … HU2) -U -HLK /3 width=5/
qed.


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

include "basic_2/reduction/cpr_lift.ma".
include "basic_2/reduction/cnr.ma".

(* CONTEXT-SENSITIVE NORMAL TERMS *******************************************)

(* Advanced properties ******************************************************)

(* Basic_1: was only: nf2_csort_lref *)
lemma cnr_lref_atom: ∀L,i. ⇩[0, i] L ≡ ⋆ → L ⊢ 𝐍⦃#i⦄.
#L #i #HL #X #H
elim (cpr_inv_lref1 … H) -H // *
#K #V1 #V2 #HLK #_ #_
lapply (ldrop_mono … HL … HLK) -L #H destruct
qed.

(* Basic_1: was: nf2_lref_abst *)
lemma cnr_lref_abst: ∀L,K,V,i. ⇩[0, i] L ≡ K. ⓛV → L ⊢ 𝐍⦃#i⦄.
#L #K #V #i #HLK #X #H
elim (cpr_inv_lref1 … H) -H // *
#K0 #V1 #V2 #HLK0 #_ #_
lapply (ldrop_mono … HLK … HLK0) -L #H destruct
qed.

(* Relocation properties ****************************************************)

(* Basic_1: was: nf2_lift *)
lemma cnr_lift: ∀L0,L,T,T0,d,e.
                L ⊢ 𝐍⦃T⦄ → ⇩[d, e] L0 ≡ L → ⇧[d, e] T ≡ T0 → L0 ⊢ 𝐍⦃T0⦄.
#L0 #L #T #T0 #d #e #HLT #HL0 #HT0 #X #H
elim (cpr_inv_lift1 … H … HL0 … HT0) -L0 #T1 #HT10 #HT1
<(HLT … HT1) in HT0; -L #HT0
>(lift_mono … HT10 … HT0) -T1 -X //
qed.

(* Note: this was missing in basic_1 *)
lemma cnr_inv_lift: ∀L0,L,T,T0,d,e.
                    L0 ⊢ 𝐍⦃T0⦄ → ⇩[d, e] L0 ≡ L → ⇧[d, e] T ≡ T0 → L ⊢ 𝐍⦃T⦄.
#L0 #L #T #T0 #d #e #HLT0 #HL0 #HT0 #X #H
elim (lift_total X d e) #X0 #HX0
lapply (cpr_lift … H … HL0 … HT0 … HX0) -L #HTX0
>(HLT0 … HTX0) in HX0; -L0 -X0 #H
>(lift_inj … H … HT0) -T0 -X -d -e //
qed-.

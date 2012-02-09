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

include "Basic_2/reducibility/cpr_lift.ma".
include "Basic_2/reducibility/cnf.ma".

(* CONTEXT-SENSITIVE NORMAL TERMS *******************************************)

(* Advanced inversion lemmas ************************************************)

(* Basic_1: was only: nf2_csort_lref *)
lemma cnf_lref_atom: ∀L,i. ⇩[0, i] L ≡ ⋆ → L  ⊢ 𝐍[#i].
#L #i #HLK #X #H
elim (cpr_inv_lref1 … H) // *
#K0 #V0 #V1 #HLK0 #_ #_ #_
lapply (ldrop_mono … HLK … HLK0) -L #H destruct
qed.

(* Basic_1: was: nf2_lref_abst *)
lemma cnf_lref_abst: ∀L,K,V,i. ⇩[0, i] L ≡ K. ⓛV → L ⊢ 𝐍[#i].
#L #K #V #i #HLK #X #H
elim (cpr_inv_lref1 … H) // *
#K0 #V0 #V1 #HLK0 #_ #_ #_
lapply (ldrop_mono … HLK … HLK0) -L #H destruct
qed.

(* Basic_1: was: nf2_abst *)
lemma cnf_abst: ∀I,L,V,W,T. L ⊢ 𝐍[W] → L. ⓑ{I} V ⊢ 𝐍[T] → L ⊢ 𝐍[ⓛW.T].
#I #L #V #W #T #HW #HT #X #H
elim (cpr_inv_abst1 … H I V) -H #W0 #T0 #HW0 #HT0 #H destruct
>(HW … HW0) -W >(HT … HT0) -T //
qed.

(* Basic_1: was only: nf2_appl_lref *)
lemma cnf_appl_simple: ∀L,V,T. L ⊢ 𝐍[V] → L ⊢ 𝐍[T] → 𝐒[T] → L ⊢ 𝐍[ⓐV.T].
#L #V #T #HV #HT #HS #X #H
elim (cpr_inv_appl1_simple … H ?) -H // #V0 #T0 #HV0 #HT0 #H destruct
>(HV … HV0) -V >(HT … HT0) -T //
qed.

(* Relocation properties ****************************************************)

(* Basic_1: was: nf2_lift *)
lemma cnf_lift: ∀L0,L,T,T0,d,e.
                L ⊢ 𝐍[T] → ⇩[d, e] L0 ≡ L → ⇧[d, e] T ≡ T0 → L0 ⊢ 𝐍[T0].
#L0 #L #T #T0 #d #e #HLT #HL0 #HT0 #X #H
elim (cpr_inv_lift … HL0 … HT0 … H) -L0 #T1 #HT10 #HT1
>(HLT … HT1) in HT0; -L #HT0
>(lift_mono … HT10 … HT0) -T1 -X //
qed.

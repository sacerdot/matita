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

include "basic_2/computation/csn.ma". (**) (* disambiguation error *)
include "basic_2/reduction/cnx_lift.ma".
include "basic_2/computation/acp.ma".

(* CONTEXT-SENSITIVE EXTENDED STRONGLY NORMALIZING TERMS ********************)

(* Relocation properties ****************************************************)

(* Basic_1: was just: sn3_lift *)
lemma csn_lift: ∀h,g,G,L2,L1,T1,d,e. ⦃G, L1⦄ ⊢ ⬊*[h, g] T1 →
                ∀T2. ⇩[d, e] L2 ≡ L1 → ⇧[d, e] T1 ≡ T2 → ⦃G, L2⦄ ⊢ ⬊*[h, g] T2.
#h #g #G #L2 #L1 #T1 #d #e #H elim H -T1 #T1 #_ #IHT1 #T2 #HL21 #HT12
@csn_intro #T #HLT2 #HT2
elim (cpx_inv_lift1 … HLT2 … HL21 … HT12) -HLT2 #T0 #HT0 #HLT10
@(IHT1 … HLT10) // -L1 -L2 #H destruct
>(lift_mono … HT0 … HT12) in HT2; -T1 /2 width=1/
qed.

(* Basic_1: was just: sn3_gen_lift *)
lemma csn_inv_lift: ∀h,g,G,L2,L1,T1,d,e. ⦃G, L1⦄ ⊢ ⬊*[h, g] T1 →
                    ∀T2. ⇩[d, e] L1 ≡ L2 → ⇧[d, e] T2 ≡ T1 → ⦃G, L2⦄ ⊢ ⬊*[h, g] T2.
#h #g #G #L2 #L1 #T1 #d #e #H elim H -T1 #T1 #_ #IHT1 #T2 #HL12 #HT21
@csn_intro #T #HLT2 #HT2
elim (lift_total T d e) #T0 #HT0
lapply (cpx_lift … HLT2 … HL12 … HT21 … HT0) -HLT2 #HLT10
@(IHT1 … HLT10) // -L1 -L2 #H destruct
>(lift_inj … HT0 … HT21) in HT2; -T1 /2 width=1/
qed.

(* Advanced properties ******************************************************)

(* Basic_1: was just: sn3_abbr *)
lemma csn_lref_bind: ∀h,g,I,G,L,K,V,i. ⇩[0, i] L ≡ K.ⓑ{I}V → ⦃G, K⦄ ⊢ ⬊*[h, g] V → ⦃G, L⦄ ⊢ ⬊*[h, g] #i.
#h #g #I #G #L #K #V #i #HLK #HV
@csn_intro #X #H #Hi
elim (cpx_inv_lref1 … H) -H
[ #H destruct elim Hi //
| -Hi * #I0 #K0 #V0 #V1 #HLK0 #HV01 #HV1
  lapply (ldrop_mono … HLK0 … HLK) -HLK #H destruct
  lapply (ldrop_fwd_ldrop2 … HLK0) -HLK0 #HLK
  @(csn_lift … HLK HV1) -HLK -HV1
  @(csn_cpx_trans … HV) -HV //
]
qed.

lemma csn_appl_simple: ∀h,g,G,L,V. ⦃G, L⦄ ⊢ ⬊*[h, g] V → ∀T1.
                       (∀T2. ⦃G, L⦄ ⊢ T1 ➡[h, g] T2 → (T1 = T2 → ⊥) → ⦃G, L⦄ ⊢ ⬊*[h, g] ⓐV.T2) →
                       𝐒⦃T1⦄ → ⦃G, L⦄ ⊢ ⬊*[h, g] ⓐV.T1.
#h #g #G #L #V #H @(csn_ind … H) -V #V #_ #IHV #T1 #IHT1 #HT1
@csn_intro #X #H1 #H2
elim (cpx_inv_appl1_simple … H1) // -H1
#V0 #T0 #HLV0 #HLT10 #H destruct
elim (eq_false_inv_tpair_dx … H2) -H2
[ -IHV -HT1 #HT10
  @(csn_cpx_trans … (ⓐV.T0)) /2 width=1/ -HLV0
  @IHT1 -IHT1 // /2 width=1/
| -HLT10 * #H #HV0 destruct
  @IHV -IHV // -HT1 /2 width=1/ -HV0
  #T2 #HLT02 #HT02
  @(csn_cpx_trans … (ⓐV.T2)) /2 width=1/ -HLV0
  @IHT1 -IHT1 // -HLT02 /2 width=1/
]
qed.

(* Advanced inversion lemmas ************************************************)

(* Basic_1: was: sn3_gen_def *)
lemma csn_inv_lref_bind: ∀h,g,I,G,L,K,V,i. ⇩[0, i] L ≡ K.ⓑ{I}V →
                         ⦃G, L⦄ ⊢ ⬊*[h, g] #i → ⦃G, K⦄ ⊢ ⬊*[h, g] V.
#h #g #I #G #L #K #V #i #HLK #Hi
elim (lift_total V 0 (i+1)) #V0 #HV0
lapply (ldrop_fwd_ldrop2 … HLK) #H0LK
@(csn_inv_lift … H0LK … HV0) -H0LK
@(csn_cpx_trans … Hi) -Hi /2 width=7/
qed-.

(* Main properties **********************************************************)

theorem csn_acp: ∀h,g. acp (cpx h g) (eq …) (csn h g).
#h #g @mk_acp
[ #G #L elim (deg_total h g 0)
  #l #Hl lapply (cnx_sort_iter … L … Hl) /2 width=2/
| @cnx_lift
| /2 width=3 by csn_fwd_flat_dx/
| /2 width=1/
]
qed.

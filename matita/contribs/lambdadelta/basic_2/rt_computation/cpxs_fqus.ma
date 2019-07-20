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

(* UNBOUND CONTEXT-SENSITIVE PARALLEL RT-COMPUTATION FOR TERMS **************)

include "basic_2/rt_transition/cpx_fqus.ma".
include "basic_2/rt_computation/cpxs_drops.ma".
include "basic_2/rt_computation/cpxs_lsubr.ma".
include "basic_2/rt_computation/cpxs_cpxs.ma".

(* Properties on supclosure *************************************************)

lemma fqu_cpxs_trans: ∀h,b,G1,G2,L1,L2,T2,U2. ⦃G2,L2⦄ ⊢ T2 ⬈*[h] U2 →
                      ∀T1. ⦃G1,L1,T1⦄ ⬂[b] ⦃G2,L2,T2⦄ →
                      ∃∃U1. ⦃G1,L1⦄ ⊢ T1 ⬈*[h] U1 & ⦃G1,L1,U1⦄ ⬂[b] ⦃G2,L2,U2⦄.
#h #b #G1 #G2 #L1 #L2 #T2 #U2 #H @(cpxs_ind_dx … H) -T2 /2 width=3 by ex2_intro/
#T #T2 #HT2 #_ #IHTU2 #T1 #HT1 elim (fqu_cpx_trans … HT1 … HT2) -T
#T #HT1 #HT2 elim (IHTU2 … HT2) -T2 /3 width=3 by cpxs_strap2, ex2_intro/
qed-.

lemma fquq_cpxs_trans: ∀h,b,G1,G2,L1,L2,T2,U2. ⦃G2,L2⦄ ⊢ T2 ⬈*[h] U2 →
                       ∀T1. ⦃G1,L1,T1⦄ ⬂⸮[b] ⦃G2,L2,T2⦄ →
                       ∃∃U1. ⦃G1,L1⦄ ⊢ T1 ⬈*[h] U1 & ⦃G1,L1,U1⦄ ⬂⸮[b] ⦃G2,L2,U2⦄.
#h #b #G1 #G2 #L1 #L2 #T2 #U2 #H @(cpxs_ind_dx … H) -T2 /2 width=3 by ex2_intro/
#T #T2 #HT2 #_ #IHTU2 #T1 #HT1 elim (fquq_cpx_trans … HT1 … HT2) -T
#T #HT1 #HT2 elim (IHTU2 … HT2) -T2 /3 width=3 by cpxs_strap2, ex2_intro/
qed-.

lemma fqup_cpxs_trans: ∀h,b,G1,G2,L1,L2,T2,U2. ⦃G2,L2⦄ ⊢ T2 ⬈*[h] U2 →
                       ∀T1. ⦃G1,L1,T1⦄ ⬂+[b] ⦃G2,L2,T2⦄ →
                       ∃∃U1. ⦃G1,L1⦄ ⊢ T1 ⬈*[h] U1 & ⦃G1,L1,U1⦄ ⬂+[b] ⦃G2,L2,U2⦄.
#h #b #G1 #G2 #L1 #L2 #T2 #U2 #H @(cpxs_ind_dx … H) -T2 /2 width=3 by ex2_intro/
#T #T2 #HT2 #_ #IHTU2 #T1 #HT1 elim (fqup_cpx_trans … HT1 … HT2) -T
#U1 #HTU1 #H2 elim (IHTU2 … H2) -T2 /3 width=3 by cpxs_strap2, ex2_intro/
qed-.

lemma fqus_cpxs_trans: ∀h,b,G1,G2,L1,L2,T2,U2. ⦃G2,L2⦄ ⊢ T2 ⬈*[h] U2 →
                       ∀T1. ⦃G1,L1,T1⦄ ⬂*[b] ⦃G2,L2,T2⦄ →
                       ∃∃U1. ⦃G1,L1⦄ ⊢ T1 ⬈*[h] U1 & ⦃G1,L1,U1⦄ ⬂*[b] ⦃G2,L2,U2⦄.
#h #b #G1 #G2 #L1 #L2 #T2 #U2 #H @(cpxs_ind_dx … H) -T2 /2 width=3 by ex2_intro/
#T #T2 #HT2 #_ #IHTU2 #T1 #HT1 elim (fqus_cpx_trans … HT1 … HT2) -T
#U1 #HTU1 #H2 elim (IHTU2 … H2) -T2 /3 width=3 by cpxs_strap2, ex2_intro/
qed-.

(* Note: a proof based on fqu_cpx_trans_tdneq might exist *)
(* Basic_2A1: uses: fqu_cpxs_trans_neq *)
lemma fqu_cpxs_trans_tdneq: ∀h,b,G1,G2,L1,L2,T1,T2. ⦃G1,L1,T1⦄ ⬂[b] ⦃G2,L2,T2⦄ →
                            ∀U2. ⦃G2,L2⦄ ⊢ T2 ⬈*[h] U2 → (T2 ≛ U2 → ⊥) →
                            ∃∃U1. ⦃G1,L1⦄ ⊢ T1 ⬈*[h] U1 & T1 ≛ U1 → ⊥ & ⦃G1,L1,U1⦄ ⬂[b] ⦃G2,L2,U2⦄.
#h #b #G1 #G2 #L1 #L2 #T1 #T2 #H elim H -G1 -G2 -L1 -L2 -T1 -T2
[ #I #G #L #V1 #V2 #HV12 #_ elim (lifts_total V2 𝐔❴1❵)
  #U2 #HVU2 @(ex3_intro … U2)
  [1,3: /3 width=7 by cpxs_delta, fqu_drop/
  | #H lapply (tdeq_inv_lref1 … H) -H
    #H destruct /2 width=5 by lifts_inv_lref2_uni_lt/
  ]
| #I #G #L #V1 #T #V2 #HV12 #H0 @(ex3_intro … (②{I}V2.T))
  [1,3: /2 width=4 by fqu_pair_sn, cpxs_pair_sn/
  | #H elim (tdeq_inv_pair … H) -H /2 width=1 by/
  ]
| #p #I #G #L #V #T1 #Hb #T2 #HT12 #H0 @(ex3_intro … (ⓑ{p,I}V.T2))
  [1,3: /2 width=4 by fqu_bind_dx, cpxs_bind/
  | #H elim (tdeq_inv_pair … H) -H /2 width=1 by/
  ]
| #p #I #G #L #V #T1 #Hb #T2 #HT12 #H0 @(ex3_intro … (ⓑ{p,I}V.T2))
  [1,3: /4 width=4 by lsubr_cpxs_trans, cpxs_bind, lsubr_unit, fqu_clear/
  | #H elim (tdeq_inv_pair … H) -H /2 width=1 by/
  ]
| #I #G #L #V #T1 #T2 #HT12 #H0 @(ex3_intro … (ⓕ{I}V.T2))
  [1,3: /2 width=4 by fqu_flat_dx, cpxs_flat/
  | #H elim (tdeq_inv_pair … H) -H /2 width=1 by/
  ]
| #I #G #L #T1 #U1 #HTU1 #T2 #HT12 #H0
  elim (cpxs_lifts_sn … HT12 (Ⓣ) … (L.ⓘ{I}) … HTU1) -HT12
  /4 width=6 by fqu_drop, drops_refl, drops_drop, tdeq_inv_lifts_bi, ex3_intro/
]
qed-.

(* Basic_2A1: uses: fquq_cpxs_trans_neq *)
lemma fquq_cpxs_trans_tdneq: ∀h,b,G1,G2,L1,L2,T1,T2. ⦃G1,L1,T1⦄ ⬂⸮[b] ⦃G2,L2,T2⦄ →
                             ∀U2. ⦃G2,L2⦄ ⊢ T2 ⬈*[h] U2 → (T2 ≛ U2 → ⊥) →
                             ∃∃U1. ⦃G1,L1⦄ ⊢ T1 ⬈*[h] U1 & T1 ≛ U1 → ⊥ & ⦃G1,L1,U1⦄ ⬂⸮[b] ⦃G2,L2,U2⦄.
#h #b #G1 #G2 #L1 #L2 #T1 #T2 #H12 elim H12 -H12
[ #H12 #U2 #HTU2 #H elim (fqu_cpxs_trans_tdneq … H12 … HTU2 H) -T2
  /3 width=4 by fqu_fquq, ex3_intro/
| * #HG #HL #HT destruct /3 width=4 by ex3_intro/
]
qed-.

(* Basic_2A1: uses: fqup_cpxs_trans_neq *)
lemma fqup_cpxs_trans_tdneq: ∀h,b,G1,G2,L1,L2,T1,T2. ⦃G1,L1,T1⦄ ⬂+[b] ⦃G2,L2,T2⦄ →
                             ∀U2. ⦃G2,L2⦄ ⊢ T2 ⬈*[h] U2 → (T2 ≛ U2 → ⊥) →
                             ∃∃U1. ⦃G1,L1⦄ ⊢ T1 ⬈*[h] U1 & T1 ≛ U1 → ⊥ & ⦃G1,L1,U1⦄ ⬂+[b] ⦃G2,L2,U2⦄.
#h #b #G1 #G2 #L1 #L2 #T1 #T2 #H @(fqup_ind_dx … H) -G1 -L1 -T1
[ #G1 #L1 #T1 #H12 #U2 #HTU2 #H elim (fqu_cpxs_trans_tdneq … H12 … HTU2 H) -T2
  /3 width=4 by fqu_fqup, ex3_intro/
| #G #G1 #L #L1 #T #T1 #H1 #_ #IH12 #U2 #HTU2 #H elim (IH12 … HTU2 H) -T2
  #U1 #HTU1 #H #H12 elim (fqu_cpxs_trans_tdneq … H1 … HTU1 H) -T1
  /3 width=8 by fqup_strap2, ex3_intro/
]
qed-.

(* Basic_2A1: uses: fqus_cpxs_trans_neq *)
lemma fqus_cpxs_trans_tdneq: ∀h,b,G1,G2,L1,L2,T1,T2. ⦃G1,L1,T1⦄ ⬂*[b] ⦃G2,L2,T2⦄ →
                             ∀U2. ⦃G2,L2⦄ ⊢ T2 ⬈*[h] U2 → (T2 ≛ U2 → ⊥) →
                             ∃∃U1. ⦃G1,L1⦄ ⊢ T1 ⬈*[h] U1 & T1 ≛ U1 → ⊥ & ⦃G1,L1,U1⦄ ⬂*[b] ⦃G2,L2,U2⦄.
#h #b #G1 #G2 #L1 #L2 #T1 #T2 #H12 #U2 #HTU2 #H elim (fqus_inv_fqup … H12) -H12
[ #H12 elim (fqup_cpxs_trans_tdneq … H12 … HTU2 H) -T2
  /3 width=4 by fqup_fqus, ex3_intro/
| * #HG #HL #HT destruct /3 width=4 by ex3_intro/
]
qed-.

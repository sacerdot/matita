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

(* UNCOUNTED CONTEXT-SENSITIVE PARALLEL RT-TRANSITION FOR TERMS *************)

include "basic_2/relocation/lifts_tdeq.ma".
include "basic_2/s_computation/fqus_fqup.ma".
include "basic_2/rt_transition/cpx_drops.ma".
include "basic_2/rt_transition/cpx_lsubr.ma".

(* Properties on supclosure *************************************************)

lemma fqu_cpx_trans: ∀h,b,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐[b] ⦃G2, L2, T2⦄ →
                     ∀U2. ⦃G2, L2⦄ ⊢ T2 ⬈[h] U2 →
                     ∃∃U1. ⦃G1, L1⦄ ⊢ T1 ⬈[h] U1 & ⦃G1, L1, U1⦄ ⊐[b] ⦃G2, L2, U2⦄.
#h #b #G1 #G2 #L1 #L2 #T1 #T2 #H elim H -G1 -G2 -L1 -L2 -T1 -T2
/3 width=3 by cpx_pair_sn, cpx_bind, cpx_flat, fqu_pair_sn, fqu_bind_dx, fqu_flat_dx, ex2_intro/
[ #I #G #L2 #V2 #X2 #HVX2
  elim (lifts_total X2 (𝐔❴1❵))
  /3 width=3 by fqu_drop, cpx_delta, ex2_intro/
| /5 width=4 by lsubr_cpx_trans, cpx_bind, lsubr_unit, fqu_clear, ex2_intro/
| #I #G #L2 #T2 #X2 #HTX2 #U2 #HTU2
  elim (cpx_lifts_sn … HTU2 (Ⓣ) … (L2.ⓘ{I}) … HTX2)
  /3 width=3 by fqu_drop, drops_refl, drops_drop, ex2_intro/
]
qed-.

lemma fquq_cpx_trans: ∀h,b,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐⸮[b] ⦃G2, L2, T2⦄ →
                      ∀U2. ⦃G2, L2⦄ ⊢ T2 ⬈[h] U2 →
                      ∃∃U1. ⦃G1, L1⦄ ⊢ T1 ⬈[h] U1 & ⦃G1, L1, U1⦄ ⊐⸮[b] ⦃G2, L2, U2⦄.
#h #b #G1 #G2 #L1 #L2 #T1 #T2 #H elim H -H
[ #HT12 #U2 #HTU2 elim (fqu_cpx_trans … HT12 … HTU2) /3 width=3 by fqu_fquq, ex2_intro/
| * #H1 #H2 #H3 destruct /2 width=3 by ex2_intro/
]
qed-.

lemma fqup_cpx_trans: ∀h,b,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐+[b] ⦃G2, L2, T2⦄ →
                      ∀U2. ⦃G2, L2⦄ ⊢ T2 ⬈[h] U2 →
                      ∃∃U1. ⦃G1, L1⦄ ⊢ T1 ⬈[h] U1 & ⦃G1, L1, U1⦄ ⊐+[b] ⦃G2, L2, U2⦄.
#h #b #G1 #G2 #L1 #L2 #T1 #T2 #H @(fqup_ind … H) -G2 -L2 -T2
[ #G2 #L2 #T2 #H12 #U2 #HTU2 elim (fqu_cpx_trans … H12 … HTU2) -T2
  /3 width=3 by fqu_fqup, ex2_intro/
| #G #G2 #L #L2 #T #T2 #_ #HT2 #IHT1 #U2 #HTU2
  elim (fqu_cpx_trans … HT2 … HTU2) -T2 #T2 #HT2 #HTU2
  elim (IHT1 … HT2) -T /3 width=7 by fqup_strap1, ex2_intro/
]
qed-.

lemma fqus_cpx_trans: ∀h,b,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐*[b] ⦃G2, L2, T2⦄ →
                      ∀U2. ⦃G2, L2⦄ ⊢ T2 ⬈[h] U2 →
                      ∃∃U1. ⦃G1, L1⦄ ⊢ T1 ⬈[h] U1 & ⦃G1, L1, U1⦄ ⊐*[b] ⦃G2, L2, U2⦄.
#h #b #G1 #G2 #L1 #L2 #T1 #T2 #H elim (fqus_inv_fqup … H) -H
[ #HT12 #U2 #HTU2 elim (fqup_cpx_trans … HT12 … HTU2) /3 width=3 by fqup_fqus, ex2_intro/
| * #H1 #H2 #H3 destruct /2 width=3 by ex2_intro/
]
qed-.

lemma fqu_cpx_trans_ntdeq: ∀h,o,b,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐[b] ⦃G2, L2, T2⦄ →
                           ∀U2. ⦃G2, L2⦄ ⊢ T2 ⬈[h] U2 → (T2 ≡[h, o] U2 → ⊥) →
                           ∃∃U1. ⦃G1, L1⦄ ⊢ T1 ⬈[h] U1 & T1 ≡[h, o] U1 → ⊥ & ⦃G1, L1, U1⦄ ⊐[b] ⦃G2, L2, U2⦄.
#h #o #b #G1 #G2 #L1 #L2 #T1 #T2 #H elim H -G1 -G2 -L1 -L2 -T1 -T2
[ #I #G #L #V1 #V2 #HV12 #_ elim (lifts_total V2 𝐔❴1❵)
  #U2 #HVU2 @(ex3_intro … U2)
  [1,3: /3 width=7 by cpx_delta, fqu_drop/
  | #H lapply (tdeq_inv_lref1 … H) -H
    #H destruct /2 width=5 by lifts_inv_lref2_uni_lt/
  ]
| #I #G #L #V1 #T #V2 #HV12 #H0 @(ex3_intro … (②{I}V2.T))
  [1,3: /2 width=4 by fqu_pair_sn, cpx_pair_sn/
  | #H elim (tdeq_inv_pair … H) -H /2 width=1 by/
  ]
| #p #I #G #L #V #T1 #T2 #HT12 #H0 @(ex3_intro … (ⓑ{p,I}V.T2))
  [1,3: /2 width=4 by fqu_bind_dx, cpx_bind/
  | #H elim (tdeq_inv_pair … H) -H /2 width=1 by/
  ]
| #p #I #G #L #V #T1 #Hb #T2 #HT12 #H0 @(ex3_intro … (ⓑ{p,I}V.T2))
  [1,3: /4 width=4 by lsubr_cpx_trans, cpx_bind, lsubr_unit, fqu_clear/
  | #H elim (tdeq_inv_pair … H) -H /2 width=1 by/
  ]
| #I #G #L #V #T1 #T2 #HT12 #H0 @(ex3_intro … (ⓕ{I}V.T2))
  [1,3: /2 width=4 by fqu_flat_dx, cpx_flat/
  | #H elim (tdeq_inv_pair … H) -H /2 width=1 by/
  ]
| #I #G #L #T1 #U1 #HTU1 #T2 #HT12 #H0
  elim (cpx_lifts_sn … HT12 (Ⓣ) … (L.ⓘ{I}) … HTU1) -HT12
  /4 width=6 by fqu_drop, drops_refl, drops_drop, tdeq_inv_lifts_bi, ex3_intro/
]
qed-.

lemma fquq_cpx_trans_ntdeq: ∀h,o,b,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐⸮[b] ⦃G2, L2, T2⦄ →
                            ∀U2. ⦃G2, L2⦄ ⊢ T2 ⬈[h] U2 → (T2 ≡[h, o] U2 → ⊥) →
                            ∃∃U1. ⦃G1, L1⦄ ⊢ T1 ⬈[h] U1 & T1 ≡[h, o] U1 → ⊥ & ⦃G1, L1, U1⦄ ⊐⸮[b] ⦃G2, L2, U2⦄.
#h #o #b #G1 #G2 #L1 #L2 #T1 #T2 #H12 elim H12 -H12 
[ #H12 #U2 #HTU2 #H elim (fqu_cpx_trans_ntdeq … H12 … HTU2 H) -T2
  /3 width=4 by fqu_fquq, ex3_intro/
| * #HG #HL #HT destruct /3 width=4 by ex3_intro/
]
qed-.

lemma fqup_cpx_trans_ntdeq: ∀h,o,b,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐+[b] ⦃G2, L2, T2⦄ →
                            ∀U2. ⦃G2, L2⦄ ⊢ T2 ⬈[h] U2 → (T2 ≡[h, o] U2 → ⊥) →
                            ∃∃U1. ⦃G1, L1⦄ ⊢ T1 ⬈[h] U1 & T1 ≡[h, o] U1 → ⊥ & ⦃G1, L1, U1⦄ ⊐+[b] ⦃G2, L2, U2⦄.
#h #o #b #G1 #G2 #L1 #L2 #T1 #T2 #H @(fqup_ind_dx … H) -G1 -L1 -T1
[ #G1 #L1 #T1 #H12 #U2 #HTU2 #H elim (fqu_cpx_trans_ntdeq … H12 … HTU2 H) -T2
  /3 width=4 by fqu_fqup, ex3_intro/
| #G #G1 #L #L1 #T #T1 #H1 #_ #IH12 #U2 #HTU2 #H elim (IH12 … HTU2 H) -T2
  #U1 #HTU1 #H #H12 elim (fqu_cpx_trans_ntdeq … H1 … HTU1 H) -T1
  /3 width=8 by fqup_strap2, ex3_intro/
]
qed-.

lemma fqus_cpx_trans_ntdeq: ∀h,o,b,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐*[b] ⦃G2, L2, T2⦄ →
                            ∀U2. ⦃G2, L2⦄ ⊢ T2 ⬈[h] U2 → (T2 ≡[h, o] U2 → ⊥) →
                            ∃∃U1. ⦃G1, L1⦄ ⊢ T1 ⬈[h] U1 & T1 ≡[h, o] U1 → ⊥ & ⦃G1, L1, U1⦄ ⊐*[b] ⦃G2, L2, U2⦄.
#h #o #b #G1 #G2 #L1 #L2 #T1 #T2 #H12 #U2 #HTU2 #H elim (fqus_inv_fqup … H12) -H12
[ #H12 elim (fqup_cpx_trans_ntdeq … H12 … HTU2 H) -T2
  /3 width=4 by fqup_fqus, ex3_intro/
| * #HG #HL #HT destruct /3 width=4 by ex3_intro/
]
qed-.


include "basic_2/reduction/lpx_drop.ma".
include "basic_2/computation/cpxs_lift.ma".
include "basic_2/rt_computation/cpxs_cpxs.ma".

(* Properties on sn extended parallel reduction for local environments ******)

lemma cpx_bind2: ∀h,o,G,L,V1,V2. ⦃G, L⦄ ⊢ V1 ⬈[h, o] V2 →
                 ∀I,T1,T2. ⦃G, L.ⓑ{I}V2⦄ ⊢ T1 ⬈[h, o] T2 →
                 ∀a. ⦃G, L⦄ ⊢ ⓑ{a,I}V1.T1 ⬈*[h, o] ⓑ{a,I}V2.T2.
/4 width=5 by lpx_cpx_trans, cpxs_bind_dx, lpx_pair/ qed.

(* Advanced properties ******************************************************)

lemma cpxs_bind2_dx: ∀h,o,G,L,V1,V2. ⦃G, L⦄ ⊢ V1 ⬈[h, o] V2 →
                     ∀I,T1,T2. ⦃G, L.ⓑ{I}V2⦄ ⊢ T1 ⬈*[h, o] T2 →
                     ∀a. ⦃G, L⦄ ⊢ ⓑ{a,I}V1.T1 ⬈*[h, o] ⓑ{a,I}V2.T2.
/4 width=5 by lpx_cpxs_trans, cpxs_bind_dx, lpx_pair/ qed.

(* Properties on supclosure *************************************************)

lemma fqu_cpxs_trans_neq: ∀h,o,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐ ⦃G2, L2, T2⦄ →
                          ∀U2. ⦃G2, L2⦄ ⊢ T2 ⬈*[h, o] U2 → (T2 = U2 → ⊥) →
                          ∃∃U1. ⦃G1, L1⦄ ⊢ T1 ⬈*[h, o] U1 & T1 = U1 → ⊥ & ⦃G1, L1, U1⦄ ⊐ ⦃G2, L2, U2⦄.
#h #o #G1 #G2 #L1 #L2 #T1 #T2 #H elim H -G1 -G2 -L1 -L2 -T1 -T2
[ #I #G #L #V1 #V2 #HV12 #_ elim (lift_total V2 0 1)
  #U2 #HVU2 @(ex3_intro … U2)
  [1,3: /3 width=7 by fqu_drop, cpxs_delta, drop_pair, drop_drop/
  | #H destruct 
    lapply (lift_inv_lref2_be … HVU2 ? ?) -HVU2 //
  ]
| #I #G #L #V1 #T #V2 #HV12 #H @(ex3_intro … (②{I}V2.T))
  [1,3: /2 width=4 by fqu_pair_sn, cpxs_pair_sn/
  | #H0 destruct /2 width=1 by/
  ]
| #a #I #G #L #V #T1 #T2 #HT12 #H @(ex3_intro … (ⓑ{a,I}V.T2))
  [1,3: /2 width=4 by fqu_bind_dx, cpxs_bind/
  | #H0 destruct /2 width=1 by/
  ]
| #I #G #L #V #T1 #T2 #HT12 #H @(ex3_intro … (ⓕ{I}V.T2))
  [1,3: /2 width=4 by fqu_flat_dx, cpxs_flat/
  | #H0 destruct /2 width=1 by/
  ]
| #G #L #K #T1 #U1 #k #HLK #HTU1 #T2 #HT12 #H elim (lift_total T2 0 (k+1))
  #U2 #HTU2 @(ex3_intro … U2)
  [1,3: /2 width=10 by cpxs_lift, fqu_drop/
  | #H0 destruct /3 width=5 by lift_inj/
]
qed-.

lemma fquq_cpxs_trans_neq: ∀h,o,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐⸮ ⦃G2, L2, T2⦄ →
                           ∀U2. ⦃G2, L2⦄ ⊢ T2 ⬈*[h, o] U2 → (T2 = U2 → ⊥) →
                           ∃∃U1. ⦃G1, L1⦄ ⊢ T1 ⬈*[h, o] U1 & T1 = U1 → ⊥ & ⦃G1, L1, U1⦄ ⊐⸮ ⦃G2, L2, U2⦄.
#h #o #G1 #G2 #L1 #L2 #T1 #T2 #H12 #U2 #HTU2 #H elim (fquq_inv_gen … H12) -H12
[ #H12 elim (fqu_cpxs_trans_neq … H12 … HTU2 H) -T2
  /3 width=4 by fqu_fquq, ex3_intro/
| * #HG #HL #HT destruct /3 width=4 by ex3_intro/
]
qed-.

lemma fqup_cpxs_trans_neq: ∀h,o,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐+ ⦃G2, L2, T2⦄ →
                           ∀U2. ⦃G2, L2⦄ ⊢ T2 ⬈*[h, o] U2 → (T2 = U2 → ⊥) →
                           ∃∃U1. ⦃G1, L1⦄ ⊢ T1 ⬈*[h, o] U1 & T1 = U1 → ⊥ & ⦃G1, L1, U1⦄ ⊐+ ⦃G2, L2, U2⦄.
#h #o #G1 #G2 #L1 #L2 #T1 #T2 #H @(fqup_ind_dx … H) -G1 -L1 -T1
[ #G1 #L1 #T1 #H12 #U2 #HTU2 #H elim (fqu_cpxs_trans_neq … H12 … HTU2 H) -T2
  /3 width=4 by fqu_fqup, ex3_intro/
| #G #G1 #L #L1 #T #T1 #H1 #_ #IH12 #U2 #HTU2 #H elim (IH12 … HTU2 H) -T2
  #U1 #HTU1 #H #H12 elim (fqu_cpxs_trans_neq … H1 … HTU1 H) -T1
  /3 width=8 by fqup_strap2, ex3_intro/
]
qed-.

lemma fqus_cpxs_trans_neq: ∀h,o,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐* ⦃G2, L2, T2⦄ →
                           ∀U2. ⦃G2, L2⦄ ⊢ T2 ⬈*[h, o] U2 → (T2 = U2 → ⊥) →
                           ∃∃U1. ⦃G1, L1⦄ ⊢ T1 ⬈*[h, o] U1 & T1 = U1 → ⊥ & ⦃G1, L1, U1⦄ ⊐* ⦃G2, L2, U2⦄.
#h #o #G1 #G2 #L1 #L2 #T1 #T2 #H12 #U2 #HTU2 #H elim (fqus_inv_gen … H12) -H12
[ #H12 elim (fqup_cpxs_trans_neq … H12 … HTU2 H) -T2
  /3 width=4 by fqup_fqus, ex3_intro/
| * #HG #HL #HT destruct /3 width=4 by ex3_intro/
]
qed-.

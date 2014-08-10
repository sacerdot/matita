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

include "basic_2/reduction/cnx_lift.ma".
include "basic_2/computation/gcp.ma".
include "basic_2/computation/csx.ma".

(* CONTEXT-SENSITIVE EXTENDED STRONGLY NORMALIZING TERMS ********************)

(* Relocation properties ****************************************************)

(* Basic_1: was just: sn3_lift *)
lemma csx_lift: ∀h,g,G,L2,L1,T1,s,d,e. ⦃G, L1⦄ ⊢ ⬊*[h, g] T1 →
                ∀T2. ⇩[s, d, e] L2 ≡ L1 → ⇧[d, e] T1 ≡ T2 → ⦃G, L2⦄ ⊢ ⬊*[h, g] T2.
#h #g #G #L2 #L1 #T1 #s #d #e #H elim H -T1 #T1 #_ #IHT1 #T2 #HL21 #HT12
@csx_intro #T #HLT2 #HT2
elim (cpx_inv_lift1 … HLT2 … HL21 … HT12) -HLT2 #T0 #HT0 #HLT10
@(IHT1 … HLT10) // -L1 -L2 #H destruct
>(lift_mono … HT0 … HT12) in HT2; -T1 /2 width=1 by/
qed.

(* Basic_1: was just: sn3_gen_lift *)
lemma csx_inv_lift: ∀h,g,G,L2,L1,T1,s,d,e. ⦃G, L1⦄ ⊢ ⬊*[h, g] T1 →
                    ∀T2. ⇩[s, d, e] L1 ≡ L2 → ⇧[d, e] T2 ≡ T1 → ⦃G, L2⦄ ⊢ ⬊*[h, g] T2.
#h #g #G #L2 #L1 #T1 #s #d #e #H elim H -T1 #T1 #_ #IHT1 #T2 #HL12 #HT21
@csx_intro #T #HLT2 #HT2
elim (lift_total T d e) #T0 #HT0
lapply (cpx_lift … HLT2 … HL12 … HT21 … HT0) -HLT2 #HLT10
@(IHT1 … HLT10) // -L1 -L2 #H destruct
>(lift_inj … HT0 … HT21) in HT2; -T1 /2 width=1 by/
qed.

(* Advanced inversion lemmas ************************************************)

(* Basic_1: was: sn3_gen_def *)
lemma csx_inv_lref_bind: ∀h,g,I,G,L,K,V,i. ⇩[i] L ≡ K.ⓑ{I}V →
                         ⦃G, L⦄ ⊢ ⬊*[h, g] #i → ⦃G, K⦄ ⊢ ⬊*[h, g] V.
#h #g #I #G #L #K #V #i #HLK #Hi
elim (lift_total V 0 (i+1))
/4 width=9 by csx_inv_lift, csx_cpx_trans, cpx_delta, drop_fwd_drop2/
qed-.

(* Advanced properties ******************************************************)

(* Basic_1: was just: sn3_abbr *)
lemma csx_lref_bind: ∀h,g,I,G,L,K,V,i. ⇩[i] L ≡ K.ⓑ{I}V → ⦃G, K⦄ ⊢ ⬊*[h, g] V → ⦃G, L⦄ ⊢ ⬊*[h, g] #i.
#h #g #I #G #L #K #V #i #HLK #HV
@csx_intro #X #H #Hi
elim (cpx_inv_lref1 … H) -H
[ #H destruct elim Hi //
| -Hi * #I0 #K0 #V0 #V1 #HLK0 #HV01 #HV1
  lapply (drop_mono … HLK0 … HLK) -HLK #H destruct
  /3 width=8 by csx_lift, csx_cpx_trans, drop_fwd_drop2/
]
qed.

lemma csx_appl_simple: ∀h,g,G,L,V. ⦃G, L⦄ ⊢ ⬊*[h, g] V → ∀T1.
                       (∀T2. ⦃G, L⦄ ⊢ T1 ➡[h, g] T2 → (T1 = T2 → ⊥) → ⦃G, L⦄ ⊢ ⬊*[h, g] ⓐV.T2) →
                       𝐒⦃T1⦄ → ⦃G, L⦄ ⊢ ⬊*[h, g] ⓐV.T1.
#h #g #G #L #V #H @(csx_ind … H) -V #V #_ #IHV #T1 #IHT1 #HT1
@csx_intro #X #H1 #H2
elim (cpx_inv_appl1_simple … H1) // -H1
#V0 #T0 #HLV0 #HLT10 #H destruct
elim (eq_false_inv_tpair_dx … H2) -H2
[ -IHV -HT1 /4 width=3 by csx_cpx_trans, cpx_pair_sn/
| -HLT10 * #H #HV0 destruct
  @IHV /4 width=3 by csx_cpx_trans, cpx_pair_sn/ (**) (* full auto 17s *)
]
qed.

lemma csx_fqu_conf: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐ ⦃G2, L2, T2⦄ →
                    ⦃G1, L1⦄ ⊢ ⬊*[h, g] T1 → ⦃G2, L2⦄ ⊢ ⬊*[h, g] T2.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 #H elim H -G1 -G2 -L1 -L2 -T1 -T2
/2 width=8 by csx_inv_lref_bind, csx_inv_lift, csx_fwd_flat_dx, csx_fwd_bind_dx, csx_fwd_pair_sn/
qed-.

lemma csx_fquq_conf: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐⸮ ⦃G2, L2, T2⦄ →
                     ⦃G1, L1⦄ ⊢ ⬊*[h, g] T1 → ⦃G2, L2⦄ ⊢ ⬊*[h, g] T2.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 #H12 #H elim (fquq_inv_gen … H12) -H12
[ /2 width=5 by csx_fqu_conf/
| * #HG #HL #HT destruct //
]
qed-.

lemma csx_fqup_conf: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐+ ⦃G2, L2, T2⦄ →
                     ⦃G1, L1⦄ ⊢ ⬊*[h, g] T1 → ⦃G2, L2⦄ ⊢ ⬊*[h, g] T2.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 #H @(fqup_ind … H) -G2 -L2 -T2
/3 width=5 by csx_fqu_conf/
qed-.

lemma csx_fqus_conf: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐* ⦃G2, L2, T2⦄ →
                     ⦃G1, L1⦄ ⊢ ⬊*[h, g] T1 → ⦃G2, L2⦄ ⊢ ⬊*[h, g] T2.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 #H12 #H elim (fqus_inv_gen … H12) -H12
[ /2 width=5 by csx_fqup_conf/
| * #HG #HL #HT destruct //
]
qed-.

(* Main properties **********************************************************)

theorem csx_gcp: ∀h,g. gcp (cpx h g) (eq …) (csx h g).
#h #g @mk_gcp
[ /3 width=13 by cnx_lift/
| #G #L elim (deg_total h g 0) /3 width=8 by cnx_sort_iter, ex_intro/
| /2 width=3 by csx_fwd_flat_dx/
]
qed.

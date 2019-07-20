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

include "static_2/s_computation/fqus_fqup.ma".
include "static_2/static/rdeq_drops.ma".
include "static_2/static/rdeq_fqup.ma".
include "static_2/static/rdeq_rdeq.ma".

(* SORT-IRRELEVANT EQUIVALENCE FOR LOCAL ENVIRONMENTS ON REFERRED ENTRIES ***)

(* Properties with extended structural successor for closures ***************)

lemma fqu_tdeq_conf: ∀b,G1,G2,L1,L2,U1,T1. ⦃G1,L1,U1⦄ ⬂[b] ⦃G2,L2,T1⦄ →
                     ∀U2. U1 ≛ U2 →
                     ∃∃L,T2. ⦃G1,L1,U2⦄ ⬂[b] ⦃G2,L,T2⦄ & L2 ≛[T1] L & T1 ≛ T2.
#b #G1 #G2 #L1 #L2 #U1 #T1 #H elim H -G1 -G2 -L1 -L2 -U1 -T1
[ #I #G #L #W #X #H >(tdeq_inv_lref1 … H) -X
  /2 width=5 by fqu_lref_O, ex3_2_intro/
| #I #G #L #W1 #U1 #X #H
  elim (tdeq_inv_pair1 … H) -H #W2 #U2 #HW12 #_ #H destruct
  /2 width=5 by fqu_pair_sn, ex3_2_intro/
| #p #I #G #L #W1 #U1 #Hb #X #H
  elim (tdeq_inv_pair1 … H) -H #W2 #U2 #HW12 #HU12 #H destruct
  /3 width=5 by rdeq_pair_refl, fqu_bind_dx, ex3_2_intro/
| #p #I #G #L #W1 #U1 #Hb #X #H
  elim (tdeq_inv_pair1 … H) -H #W2 #U2 #HW12 #HU12 #H destruct
  /3 width=5 by fqu_clear, ex3_2_intro/
| #I #G #L #W1 #U1 #X #H
  elim (tdeq_inv_pair1 … H) -H #W2 #U2 #_ #HU12 #H destruct
  /2 width=5 by fqu_flat_dx, ex3_2_intro/
| #I #G #L #T1 #U1 #HTU1 #U2 #HU12
  elim (tdeq_inv_lifts_sn … HU12 … HTU1) -U1
  /3 width=5 by fqu_drop, ex3_2_intro/
]
qed-.

lemma tdeq_fqu_trans: ∀b,G1,G2,L1,L2,U1,T1. ⦃G1,L1,U1⦄ ⬂[b] ⦃G2,L2,T1⦄ →
                      ∀U2. U2 ≛ U1 →
                      ∃∃L,T2. ⦃G1,L1,U2⦄ ⬂[b] ⦃G2,L,T2⦄ & T2 ≛ T1 & L ≛[T1] L2.
#b #G1 #G2 #L1 #L2 #U1 #T1 #H12 #U2 #HU21
elim (fqu_tdeq_conf … H12 U2) -H12
/3 width=5 by rdeq_sym, tdeq_sym, ex3_2_intro/
qed-.

(* Basic_2A1: uses: lleq_fqu_trans *)
lemma rdeq_fqu_trans: ∀b,G1,G2,L2,K2,T,U. ⦃G1,L2,T⦄ ⬂[b] ⦃G2,K2,U⦄ →
                      ∀L1. L1 ≛[T] L2 →
                      ∃∃K1,U0. ⦃G1,L1,T⦄ ⬂[b] ⦃G2,K1,U0⦄ & U0 ≛ U & K1 ≛[U] K2.
#b #G1 #G2 #L2 #K2 #T #U #H elim H -G1 -G2 -L2 -K2 -T -U
[ #I #G #L2 #V2 #L1 #H elim (rdeq_inv_zero_pair_dx … H) -H
  #K1 #V1 #HV1 #HV12 #H destruct
  /3 width=7 by tdeq_rdeq_conf, fqu_lref_O, ex3_2_intro/
| * [ #p ] #I #G #L2 #V #T #L1 #H
  [ elim (rdeq_inv_bind … H)
  | elim (rdeq_inv_flat … H)
  ] -H
  /2 width=5 by fqu_pair_sn, ex3_2_intro/
| #p #I #G #L2 #V #T #Hb #L1 #H elim (rdeq_inv_bind … H) -H
  /3 width=5 by fqu_bind_dx, ex3_2_intro/
| #p #I #G #L2 #V #T #Hb #L1 #H elim (rdeq_inv_bind_void … H) -H
  /3 width=5 by fqu_clear, ex3_2_intro/
| #I #G #L2 #V #T #L1 #H elim (rdeq_inv_flat … H) -H
  /2 width=5 by fqu_flat_dx, ex3_2_intro/
| #I #G #L2 #T #U #HTU #Y #HU
  elim (rdeq_fwd_dx … HU) #L1 #V1 #H destruct
  /5 width=14 by rdeq_inv_lifts_bi, fqu_drop, drops_refl, drops_drop, ex3_2_intro/
]
qed-.

(* Properties with optional structural successor for closures ***************)

lemma tdeq_fquq_trans: ∀b,G1,G2,L1,L2,U1,T1. ⦃G1,L1,U1⦄ ⬂⸮[b] ⦃G2,L2,T1⦄ →
                       ∀U2. U2 ≛ U1 →
                       ∃∃L,T2. ⦃G1,L1,U2⦄ ⬂⸮[b] ⦃G2,L,T2⦄ & T2 ≛ T1 & L ≛[T1] L2.
#b #G1 #G2 #L1 #L2 #U1 #T1 #H elim H -H
[ #H #U2 #HU21 elim (tdeq_fqu_trans … H … HU21) -U1
  /3 width=5 by fqu_fquq, ex3_2_intro/
| * #HG #HL #HT destruct /2 width=5 by ex3_2_intro/
]
qed-.

(* Basic_2A1: was just: lleq_fquq_trans *)
lemma rdeq_fquq_trans: ∀b,G1,G2,L2,K2,T,U. ⦃G1,L2,T⦄ ⬂⸮[b] ⦃G2,K2,U⦄ →
                       ∀L1. L1 ≛[T] L2 →
                       ∃∃K1,U0. ⦃G1,L1,T⦄ ⬂⸮[b] ⦃G2,K1,U0⦄ & U0 ≛ U & K1 ≛[U] K2.
#b #G1 #G2 #L2 #K2 #T #U #H elim H -H
[ #H #L1 #HL12 elim (rdeq_fqu_trans … H … HL12) -L2 /3 width=5 by fqu_fquq, ex3_2_intro/
| * #HG #HL #HT destruct /2 width=5 by ex3_2_intro/
]
qed-.

(* Properties with plus-iterated structural successor for closures **********)

(* Basic_2A1: was just: lleq_fqup_trans *)
lemma rdeq_fqup_trans: ∀b,G1,G2,L2,K2,T,U. ⦃G1,L2,T⦄ ⬂+[b] ⦃G2,K2,U⦄ →
                       ∀L1. L1 ≛[T] L2 →
                       ∃∃K1,U0. ⦃G1,L1,T⦄ ⬂+[b] ⦃G2,K1,U0⦄ & U0 ≛ U & K1 ≛[U] K2.
#b #G1 #G2 #L2 #K2 #T #U #H @(fqup_ind … H) -G2 -K2 -U
[ #G2 #K2 #U #HTU #L1 #HL12 elim (rdeq_fqu_trans … HTU … HL12) -L2
  /3 width=5 by fqu_fqup, ex3_2_intro/
| #G #G2 #K #K2 #U #U2 #_ #HU2 #IHTU #L1 #HL12
  elim (IHTU … HL12) -L2 #K0 #U0 #HTU #HU0 #HK0
  elim (rdeq_fqu_trans … HU2 … HK0) -K #K1 #U1 #HU1 #HU12 #HK12
  elim (tdeq_fqu_trans … HU1 … HU0) -U #K3 #U3 #HU03 #HU31 #HK31
  @(ex3_2_intro … K3 U3) (**) (* full auto too slow *)
  /3 width=5 by rdeq_trans, tdeq_rdeq_conf, fqup_strap1, tdeq_trans/
]
qed-.

lemma tdeq_fqup_trans: ∀b,G1,G2,L1,L2,U1,T1. ⦃G1,L1,U1⦄ ⬂+[b] ⦃G2,L2,T1⦄ →
                       ∀U2. U2 ≛ U1 →
                       ∃∃L,T2. ⦃G1,L1,U2⦄ ⬂+[b] ⦃G2,L,T2⦄ & T2 ≛ T1 & L ≛[T1] L2.
#b #G1 #G2 #L1 #L2 #U1 #T1 #H @(fqup_ind_dx … H) -G1 -L1 -U1
[ #G1 #L1 #U1 #H #U2 #HU21 elim (tdeq_fqu_trans … H … HU21) -U1
  /3 width=5 by fqu_fqup, ex3_2_intro/
| #G1 #G #L1 #L #U1 #U #H #_ #IH #U2 #HU21
  elim (tdeq_fqu_trans … H … HU21) -U1 #L0 #T #H1 #HTU #HL0
  lapply (tdeq_rdeq_div … HTU … HL0) -HL0 #HL0
  elim (IH … HTU) -U #K2 #U1 #H2 #HUT1 #HKL2
  elim (rdeq_fqup_trans … H2 … HL0) -L #K #U #H2 #HU1 #HK2
  lapply (tdeq_rdeq_conf … HUT1 … HK2) -HK2 #HK2
  /3 width=7 by rdeq_trans, fqup_strap2, tdeq_trans, ex3_2_intro/
]
qed-.

(* Properties with star-iterated structural successor for closures **********)

lemma tdeq_fqus_trans: ∀b,G1,G2,L1,L2,U1,T1. ⦃G1,L1,U1⦄ ⬂*[b] ⦃G2,L2,T1⦄ →
                       ∀U2. U2 ≛ U1 →
                       ∃∃L,T2. ⦃G1,L1,U2⦄ ⬂*[b] ⦃G2,L,T2⦄ & T2 ≛ T1 & L ≛[T1] L2.
#b #G1 #G2 #L1 #L2 #U1 #T1 #H #U2 #HU21 elim(fqus_inv_fqup … H) -H
[ #H elim (tdeq_fqup_trans … H … HU21) -U1 /3 width=5 by fqup_fqus, ex3_2_intro/
| * #HG #HL #HT destruct /2 width=5 by ex3_2_intro/
]
qed-.

(* Basic_2A1: was just: lleq_fqus_trans *)
lemma rdeq_fqus_trans: ∀b,G1,G2,L2,K2,T,U. ⦃G1,L2,T⦄ ⬂*[b] ⦃G2,K2,U⦄ →
                       ∀L1. L1 ≛[T] L2 →
                       ∃∃K1,U0. ⦃G1,L1,T⦄ ⬂*[b] ⦃G2,K1,U0⦄ & U0 ≛ U & K1 ≛[U] K2.
#b #G1 #G2 #L2 #K2 #T #U #H #L1 #HL12 elim(fqus_inv_fqup … H) -H
[ #H elim (rdeq_fqup_trans … H … HL12) -L2 /3 width=5 by fqup_fqus, ex3_2_intro/
| * #HG #HL #HT destruct /2 width=5 by ex3_2_intro/
]
qed-.

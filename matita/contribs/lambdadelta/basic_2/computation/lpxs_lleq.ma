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

include "basic_2/multiple/lleq_lleq.ma".
include "basic_2/reduction/lpx_lleq.ma".
include "basic_2/computation/cpxs_lreq.ma".
include "basic_2/computation/lpxs_drop.ma".
include "basic_2/computation/lpxs_cpxs.ma".

(* SN EXTENDED PARALLEL COMPUTATION FOR LOCAL ENVIRONMENTS ******************)

(* Properties on lazy equivalence for local environments ********************)

lemma lleq_lpxs_trans: ∀h,o,G,L2,K2. ⦃G, L2⦄ ⊢ ➡*[h, o] K2 →
                       ∀L1,T,l. L1 ≡[T, l] L2 →
                       ∃∃K1. ⦃G, L1⦄ ⊢ ➡*[h, o] K1 & K1 ≡[T, l] K2.
#h #o #G #L2 #K2 #H @(lpxs_ind … H) -K2 /2 width=3 by ex2_intro/
#K #K2 #_ #HK2 #IH #L1 #T #l #HT elim (IH … HT) -L2
#L #HL1 #HT elim (lleq_lpx_trans … HK2 … HT) -K
/3 width=3 by lpxs_strap1, ex2_intro/
qed-.

lemma lpxs_nlleq_inv_step_sn: ∀h,o,G,L1,L2,T,l. ⦃G, L1⦄ ⊢ ➡*[h, o] L2 → (L1 ≡[T, l] L2 → ⊥) →
                              ∃∃L,L0. ⦃G, L1⦄ ⊢ ➡[h, o] L & L1 ≡[T, l] L → ⊥ & ⦃G, L⦄ ⊢ ➡*[h, o] L0 & L0 ≡[T, l] L2.
#h #o #G #L1 #L2 #T #l #H @(lpxs_ind_dx … H) -L1
[ #H elim H -H //
| #L1 #L #H1 #H2 #IH2 #H12 elim (lleq_dec T L1 L l) #H
  [ -H1 -H2 elim IH2 -IH2 /3 width=3 by lleq_trans/ -H12
    #L0 #L3 #H1 #H2 #H3 #H4 lapply (lleq_nlleq_trans … H … H2) -H2
    #H2 elim (lleq_lpx_trans … H1 … H) -L
    #L #H1 #H lapply (nlleq_lleq_div … H … H2) -H2
    #H2 elim (lleq_lpxs_trans … H3 … H) -L0
    /3 width=8 by lleq_trans, ex4_2_intro/
  | -H12 -IH2 /3 width=6 by ex4_2_intro/
  ]
]
qed-.

lemma lpxs_lleq_fqu_trans: ∀h,o,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐ ⦃G2, L2, T2⦄ →
                           ∀K1. ⦃G1, K1⦄ ⊢ ➡*[h, o] L1 → K1 ≡[T1, 0] L1 →
                           ∃∃K2. ⦃G1, K1, T1⦄ ⊐ ⦃G2, K2, T2⦄ & ⦃G2, K2⦄ ⊢ ➡*[h, o] L2 & K2 ≡[T2, 0] L2.
#h #o #G1 #G2 #L1 #L2 #T1 #T2 #H elim H -G1 -G2 -L1 -L2 -T1 -T2
[ #I #G1 #L1 #V1 #X #H1 #H2 elim (lpxs_inv_pair2 … H1) -H1
  #K0 #V0 #H1KL1 #_ #H destruct
  elim (lleq_inv_lref_ge_dx … H2 ? I L1 V1) -H2 //
  #K1 #H #H2KL1 lapply (drop_inv_O2 … H) -H #H destruct
  /2 width=4 by fqu_lref_O, ex3_intro/
| * [ #a ] #I #G1 #L1 #V1 #T1 #K1 #HLK1 #H
  [ elim (lleq_inv_bind … H)
  | elim (lleq_inv_flat … H)
  ] -H /2 width=4 by fqu_pair_sn, ex3_intro/
| #a #I #G1 #L1 #V1 #T1 #K1 #HLK1 #H elim (lleq_inv_bind_O … H) -H
  /3 width=4 by lpxs_pair, fqu_bind_dx, ex3_intro/
| #I #G1 #L1 #V1 #T1 #K1 #HLK1 #H elim (lleq_inv_flat … H) -H
  /2 width=4 by fqu_flat_dx, ex3_intro/
| #G1 #L1 #L #T1 #U1 #k #HL1 #HTU1 #K1 #H1KL1 #H2KL1
  elim (drop_O1_le (Ⓕ) (k+1) K1)
  [ #K #HK1 lapply (lleq_inv_lift_le … H2KL1 … HK1 HL1 … HTU1 ?) -H2KL1 //
    #H2KL elim (lpxs_drop_trans_O1 … H1KL1 … HL1) -L1
    #K0 #HK10 #H1KL lapply (drop_mono … HK10 … HK1) -HK10 #H destruct
    /3 width=4 by fqu_drop, ex3_intro/
  | lapply (drop_fwd_length_le2 … HL1) -L -T1 -o
    lapply (lleq_fwd_length … H2KL1) //
  ]
]
qed-.

lemma lpxs_lleq_fquq_trans: ∀h,o,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐⸮ ⦃G2, L2, T2⦄ →
                            ∀K1. ⦃G1, K1⦄ ⊢ ➡*[h, o] L1 → K1 ≡[T1, 0] L1 →
                            ∃∃K2. ⦃G1, K1, T1⦄ ⊐⸮ ⦃G2, K2, T2⦄ & ⦃G2, K2⦄ ⊢ ➡*[h, o] L2 & K2 ≡[T2, 0] L2.
#h #o #G1 #G2 #L1 #L2 #T1 #T2 #H #K1 #H1KL1 #H2KL1
elim (fquq_inv_gen … H) -H
[ #H elim (lpxs_lleq_fqu_trans … H … H1KL1 H2KL1) -L1
  /3 width=4 by fqu_fquq, ex3_intro/
| * #HG #HL #HT destruct /2 width=4 by ex3_intro/
]
qed-.

lemma lpxs_lleq_fqup_trans: ∀h,o,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐+ ⦃G2, L2, T2⦄ →
                            ∀K1. ⦃G1, K1⦄ ⊢ ➡*[h, o] L1 → K1 ≡[T1, 0] L1 →
                            ∃∃K2. ⦃G1, K1, T1⦄ ⊐+ ⦃G2, K2, T2⦄ & ⦃G2, K2⦄ ⊢ ➡*[h, o] L2 & K2 ≡[T2, 0] L2.
#h #o #G1 #G2 #L1 #L2 #T1 #T2 #H @(fqup_ind … H) -G2 -L2 -T2
[ #G2 #L2 #T2 #H #K1 #H1KL1 #H2KL1 elim (lpxs_lleq_fqu_trans … H … H1KL1 H2KL1) -L1
  /3 width=4 by fqu_fqup, ex3_intro/
| #G #G2 #L #L2 #T #T2 #_ #HT2 #IHT1 #K1 #H1KL1 #H2KL1 elim (IHT1 … H2KL1) // -L1
  #K #HT1 #H1KL #H2KL elim (lpxs_lleq_fqu_trans … HT2 … H1KL H2KL) -L
  /3 width=5 by fqup_strap1, ex3_intro/
]
qed-.

lemma lpxs_lleq_fqus_trans: ∀h,o,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐* ⦃G2, L2, T2⦄ →
                            ∀K1. ⦃G1, K1⦄ ⊢ ➡*[h, o] L1 → K1 ≡[T1, 0] L1 →
                            ∃∃K2. ⦃G1, K1, T1⦄ ⊐* ⦃G2, K2, T2⦄ & ⦃G2, K2⦄ ⊢ ➡*[h, o] L2 & K2 ≡[T2, 0] L2.
#h #o #G1 #G2 #L1 #L2 #T1 #T2 #H #K1 #H1KL1 #H2KL1
elim (fqus_inv_gen … H) -H
[ #H elim (lpxs_lleq_fqup_trans … H … H1KL1 H2KL1) -L1
  /3 width=4 by fqup_fqus, ex3_intro/
| * #HG #HL #HT destruct /2 width=4 by ex3_intro/
]
qed-.

fact lreq_lpxs_trans_lleq_aux: ∀h,o,G,L1,L0,l,k. L1 ⩬[l, k] L0 → k = ∞ →
                               ∀L2. ⦃G, L0⦄ ⊢ ➡*[h, o] L2 →
                               ∃∃L. L ⩬[l, k] L2 & ⦃G, L1⦄ ⊢ ➡*[h, o] L &
                                    (∀T. L0 ≡[T, l] L2 ↔ L1 ≡[T, l] L).
#h #o #G #L1 #L0 #l #k #H elim H -L1 -L0 -l -k
[ #l #k #_ #L2 #H >(lpxs_inv_atom1 … H) -H
  /3 width=5 by ex3_intro, conj/
| #I1 #I0 #L1 #L0 #V1 #V0 #_ #_ #Hm destruct
| #I #L1 #L0 #V1 #k #HL10 #IHL10 #Hm #Y #H
  elim (lpxs_inv_pair1 … H) -H #L2 #V2 #HL02 #HV02 #H destruct
  lapply (ysucc_inv_Y_dx … Hm) -Hm #Hm
  elim (IHL10 … HL02) // -IHL10 -HL02 #L #HL2 #HL1 #IH
  @(ex3_intro … (L.ⓑ{I}V2)) /3 width=3 by lpxs_pair, lreq_cpxs_trans, lreq_pair/
  #T elim (IH T) #HL0dx #HL0sn
  @conj #H @(lleq_lreq_repl … H) -H /3 width=1 by lreq_sym, lreq_pair_O_Y/
| #I1 #I0 #L1 #L0 #V1 #V0 #l #k #HL10 #IHL10 #Hm #Y #H
  elim (lpxs_inv_pair1 … H) -H #L2 #V2 #HL02 #HV02 #H destruct
  elim (IHL10 … HL02) // -IHL10 -HL02 #L #HL2 #HL1 #IH
  @(ex3_intro … (L.ⓑ{I1}V1)) /3 width=1 by lpxs_pair, lreq_succ/
  #T elim (IH T) #HL0dx #HL0sn
  @conj #H @(lleq_lreq_repl … H) -H /3 width=1 by lreq_sym, lreq_succ/
]
qed-.

lemma lreq_lpxs_trans_lleq: ∀h,o,G,L1,L0,l. L1 ⩬[l, ∞] L0 →
                            ∀L2. ⦃G, L0⦄ ⊢ ➡*[h, o] L2 →
                            ∃∃L. L ⩬[l, ∞] L2 & ⦃G, L1⦄ ⊢ ➡*[h, o] L &
                                 (∀T. L0 ≡[T, l] L2 ↔ L1 ≡[T, l] L).
/2 width=1 by lreq_lpxs_trans_lleq_aux/ qed-.

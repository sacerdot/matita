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

include "basic_2/relocation/lexs_length.ma".
include "basic_2/static/fsle_fsle.ma".
include "basic_2/static/lfxs_drops.ma".
include "basic_2/static/lfxs_lfxs.ma".

(* GENERIC EXTENSION ON REFERRED ENTRIES OF A CONTEXT-SENSITIVE REALTION ****)

definition R_fsge_compatible: predicate (relation3 …) ≝ λRN.
                              ∀L,T1,T2. RN L T1 T2 → ⦃L, T2⦄ ⊆ ⦃L, T1⦄.

definition lfxs_fsge_compatible: predicate (relation3 …) ≝ λRN.
                                 ∀L1,L2,T. L1 ⪤*[RN, T] L2 → ⦃L2, T⦄ ⊆ ⦃L1, T⦄.

definition lfxs_fsle_compatible: predicate (relation3 …) ≝ λRN.
                                 ∀L1,L2,T. L1 ⪤*[RN, T] L2 → ⦃L1, T⦄ ⊆ ⦃L2, T⦄.

(* Basic inversions with free variables inclusion for restricted closures ***)

lemma frees_lexs_conf: ∀R. lfxs_fsge_compatible R →
                       ∀L1,T,f1. L1 ⊢ 𝐅*⦃T⦄ ≡ f1 →
                       ∀L2. L1 ⪤*[cext2 R, cfull, f1] L2 →
                       ∃∃f2. L2 ⊢ 𝐅*⦃T⦄ ≡ f2 & f2 ⊆ f1.
#R #HR #L1 #T #f1 #Hf1 #L2 #H1L
lapply (HR L1 L2 T ?) /2 width=3 by ex2_intro/ #H2L
@(fsle_frees_trans_eq … H2L … Hf1) /3 width=4 by lexs_fwd_length, sym_eq/
qed-.

(* Properties with free variables inclusion for restricted closures *********)

(* Note: we just need lveq_inv_refl: ∀L,n1,n2. L ≋ⓧ*[n1, n2] L → ∧∧ 0 = n1 & 0 = n2 *)
lemma fsge_lfxs_trans: ∀R,L1,T1,T2. ⦃L1, T1⦄ ⊆ ⦃L1, T2⦄ →
                       ∀L2. L1 ⪤*[R, T2] L2 → L1 ⪤*[R, T1] L2.
#R #L1 #T1 #T2 * #n1 #n2 #f1 #f2 #Hf1 #Hf2 #Hn #Hf #L2 #HL12
elim (lveq_inj_length … Hn ?) // #H1 #H2 destruct
/4 width=5 by lfxs_inv_frees, sle_lexs_trans, ex2_intro/
qed-.

lemma lfxs_sym: ∀R. lfxs_fsge_compatible R →
                (∀L1,L2,T1,T2. R L1 T1 T2 → R L2 T2 T1) →
                ∀T. symmetric … (lfxs R T).
#R #H1R #H2R #T #L1 #L2
* #f1 #Hf1 #HL12
elim (frees_lexs_conf … Hf1 … HL12) -Hf1 //
/5 width=5 by sle_lexs_trans, lexs_sym, cext2_sym, ex2_intro/
qed-.

lemma lfxs_pair_sn_split: ∀R1,R2. (∀L. reflexive … (R1 L)) → (∀L. reflexive … (R2 L)) →
                          lfxs_fsge_compatible R1 →
                          ∀L1,L2,V. L1 ⪤*[R1, V] L2 → ∀I,T.
                          ∃∃L. L1 ⪤*[R1, ②{I}V.T] L & L ⪤*[R2, V] L2.
#R1 #R2 #HR1 #HR2 #HR #L1 #L2 #V * #f #Hf #HL12 * [ #p ] #I #T
[ elim (frees_total L1 (ⓑ{p,I}V.T)) #g #Hg
  elim (frees_inv_bind … Hg) #y1 #y2 #H #_ #Hy
| elim (frees_total L1 (ⓕ{I}V.T)) #g #Hg
  elim (frees_inv_flat … Hg) #y1 #y2 #H #_ #Hy
]
lapply(frees_mono … H … Hf) -H #H1
lapply (sor_eq_repl_back1 … Hy … H1) -y1 #Hy
lapply (sor_inv_sle_sn … Hy) -y2 #Hfg
elim (lexs_sle_split (cext2 R1) (cext2 R2) … HL12 … Hfg) -HL12 /2 width=1 by ext2_refl/ #L #HL1 #HL2
lapply (sle_lexs_trans … HL1 … Hfg) // #H
elim (frees_lexs_conf … Hf … H) -Hf -H
/4 width=7 by sle_lexs_trans, ex2_intro/
qed-.

lemma lfxs_flat_dx_split: ∀R1,R2. (∀L. reflexive … (R1 L)) → (∀L. reflexive … (R2 L)) →
                          lfxs_fsge_compatible R1 →
                          ∀L1,L2,T. L1 ⪤*[R1, T] L2 → ∀I,V.
                          ∃∃L. L1 ⪤*[R1, ⓕ{I}V.T] L & L ⪤*[R2, T] L2.
#R1 #R2 #HR1 #HR2 #HR #L1 #L2 #T * #f #Hf #HL12 #I #V
elim (frees_total L1 (ⓕ{I}V.T)) #g #Hg
elim (frees_inv_flat … Hg) #y1 #y2 #_ #H #Hy
lapply(frees_mono … H … Hf) -H #H2
lapply (sor_eq_repl_back2 … Hy … H2) -y2 #Hy
lapply (sor_inv_sle_dx … Hy) -y1 #Hfg
elim (lexs_sle_split (cext2 R1) (cext2 R2) … HL12 … Hfg) -HL12 /2 width=1 by ext2_refl/ #L #HL1 #HL2
lapply (sle_lexs_trans … HL1 … Hfg) // #H
elim (frees_lexs_conf … Hf … H) -Hf -H
/4 width=7 by sle_lexs_trans, ex2_intro/
qed-.

lemma lfxs_bind_dx_split: ∀R1,R2. (∀L. reflexive … (R1 L)) → (∀L. reflexive … (R2 L)) →
                          lfxs_fsge_compatible R1 →
                          ∀I,L1,L2,V1,T. L1.ⓑ{I}V1 ⪤*[R1, T] L2 → ∀p.
                          ∃∃L,V. L1 ⪤*[R1, ⓑ{p,I}V1.T] L & L.ⓑ{I}V ⪤*[R2, T] L2 & R1 L1 V1 V.
#R1 #R2 #HR1 #HR2 #HR #I #L1 #L2 #V1 #T * #f #Hf #HL12 #p
elim (frees_total L1 (ⓑ{p,I}V1.T)) #g #Hg
elim (frees_inv_bind … Hg) #y1 #y2 #_ #H #Hy
lapply(frees_mono … H … Hf) -H #H2
lapply (tl_eq_repl … H2) -H2 #H2
lapply (sor_eq_repl_back2 … Hy … H2) -y2 #Hy
lapply (sor_inv_sle_dx … Hy) -y1 #Hfg
lapply (sle_inv_tl_sn … Hfg) -Hfg #Hfg
elim (lexs_sle_split (cext2 R1) (cext2 R2) … HL12 … Hfg) -HL12 /2 width=1 by ext2_refl/ #Y #H #HL2
lapply (sle_lexs_trans … H … Hfg) // #H0
elim (lexs_inv_next1 … H) -H #Z #L #HL1 #H
elim (ext2_inv_pair_sn … H) -H #V #HV #H1 #H2 destruct
elim (frees_lexs_conf … Hf … H0) -Hf -H0
/4 width=7 by sle_lexs_trans, ex3_2_intro, ex2_intro/
qed-.

lemma lfxs_bind_dx_split_void: ∀R1,R2. (∀L. reflexive … (R1 L)) → (∀L. reflexive … (R2 L)) →
                               lfxs_fsge_compatible R1 →
                               ∀L1,L2,T. L1.ⓧ ⪤*[R1, T] L2 → ∀p,I,V.
                               ∃∃L. L1 ⪤*[R1, ⓑ{p,I}V.T] L & L.ⓧ ⪤*[R2, T] L2.
#R1 #R2 #HR1 #HR2 #HR #L1 #L2 #T * #f #Hf #HL12 #p #I #V
elim (frees_total L1 (ⓑ{p,I}V.T)) #g #Hg
elim (frees_inv_bind_void … Hg) #y1 #y2 #_ #H #Hy
lapply(frees_mono … H … Hf) -H #H2
lapply (tl_eq_repl … H2) -H2 #H2
lapply (sor_eq_repl_back2 … Hy … H2) -y2 #Hy
lapply (sor_inv_sle_dx … Hy) -y1 #Hfg
lapply (sle_inv_tl_sn … Hfg) -Hfg #Hfg
elim (lexs_sle_split (cext2 R1) (cext2 R2) … HL12 … Hfg) -HL12 /2 width=1 by ext2_refl/ #Y #H #HL2
lapply (sle_lexs_trans … H … Hfg) // #H0
elim (lexs_inv_next1 … H) -H #Z #L #HL1 #H
elim (ext2_inv_unit_sn … H) -H #H destruct
elim (frees_lexs_conf … Hf … H0) -Hf -H0
/4 width=7 by sle_lexs_trans, ex2_intro/ (* note: 2 ex2_intro *)
qed-.

(* Main properties with free variables inclusion for restricted closures ****)

theorem lfxs_conf: ∀R1,R2.
                   lfxs_fsge_compatible R1 →
                   lfxs_fsge_compatible R2 →
                   R_confluent2_lfxs R1 R2 R1 R2 →
                   ∀T. confluent2 … (lfxs R1 T) (lfxs R2 T).
#R1 #R2 #HR1 #HR2 #HR12 #T #L0 #L1 * #f1 #Hf1 #HL01 #L2 * #f #Hf #HL02
lapply (frees_mono … Hf1 … Hf) -Hf1 #Hf12
lapply (lexs_eq_repl_back … HL01 … Hf12) -f1 #HL01
elim (lexs_conf … HL01 … HL02) /2 width=3 by ex2_intro/ [ | -HL01 -HL02 ]
[ #L #HL1 #HL2
  elim (frees_lexs_conf … Hf … HL01) // -HR1 -HL01 #f1 #Hf1 #H1
  elim (frees_lexs_conf … Hf … HL02) // -HR2 -HL02 #f2 #Hf2 #H2
  lapply (sle_lexs_trans … HL1 … H1) // -HL1 -H1 #HL1
  lapply (sle_lexs_trans … HL2 … H2) // -HL2 -H2 #HL2
  /3 width=5 by ex2_intro/
| #g * #I0 [2: #V0 ] #K0 #n #HLK0 #Hgf #Z1 #H1 #Z2 #H2 #K1 #HK01 #K2 #HK02
  [ elim (ext2_inv_pair_sn … H1) -H1 #V1 #HV01 #H destruct
    elim (ext2_inv_pair_sn … H2) -H2 #V2 #HV02 #H destruct
    elim (frees_inv_drops_next … Hf … HLK0 … Hgf) -Hf -HLK0 -Hgf #g0 #Hg0 #H0
    lapply (sle_lexs_trans … HK01 … H0) // -HK01 #HK01
    lapply (sle_lexs_trans … HK02 … H0) // -HK02 #HK02
    elim (HR12 … HV01 … HV02 K1 … K2) /3 width=3 by ext2_pair, ex2_intro/
  | lapply (ext2_inv_unit_sn … H1) -H1 #H destruct
    lapply (ext2_inv_unit_sn … H2) -H2 #H destruct
    /3 width=3 by ext2_unit, ex2_intro/
  ]
]
qed-.

theorem lfxs_trans_fsle: ∀R1,R2,R3.
                         lfxs_fsle_compatible R1 → lfxs_transitive_next R1 R2 R3 →
                         ∀L1,L,T. L1 ⪤*[R1, T] L →
                         ∀L2. L ⪤*[R2, T] L2 → L1 ⪤*[R3, T] L2.
#R1 #R2 #R3 #H1R #H2R #L1 #L #T #H
lapply (H1R … H) -H1R #H0
cases H -H #f1 #Hf1 #HL1 #L2 * #f2 #Hf2 #HL2
lapply (fsle_inv_frees_eq … H0 … Hf1 … Hf2) -H0 -Hf2
/4 width=14 by lexs_trans_gen, lexs_fwd_length, sle_lexs_trans, ex2_intro/
qed-.

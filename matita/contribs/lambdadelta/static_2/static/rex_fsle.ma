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

include "static_2/relocation/sex_length.ma".
include "static_2/static/fsle_fsle.ma".
include "static_2/static/rex_drops.ma".
include "static_2/static/rex_rex.ma".

(* GENERIC EXTENSION ON REFERRED ENTRIES OF A CONTEXT-SENSITIVE REALTION ****)

definition R_fsge_compatible: predicate (relation3 …) ≝ λRN.
           ∀L,T1,T2. RN L T1 T2 → ❨L,T2❩ ⊆ ❨L,T1❩.

definition rex_fsge_compatible: predicate (relation3 …) ≝ λRN.
           ∀L1,L2,T. L1 ⪤[RN,T] L2 → ❨L2,T❩ ⊆ ❨L1,T❩.

definition rex_fsle_compatible: predicate (relation3 …) ≝ λRN.
           ∀L1,L2,T. L1 ⪤[RN,T] L2 → ❨L1,T❩ ⊆ ❨L2,T❩.

(* Basic inversions with free variables inclusion for restricted closures ***)

lemma frees_sex_conf_fsge (R):
      rex_fsge_compatible R →
      ∀L1,T,f1. L1 ⊢ 𝐅+❨T❩ ≘ f1 →
      ∀L2. L1 ⪤[cext2 R,cfull,f1] L2 →
      ∃∃f2. L2 ⊢ 𝐅+❨T❩ ≘ f2 & f2 ⊆ f1.
#R #HR #L1 #T #f1 #Hf1 #L2 #H1L
lapply (HR L1 L2 T ?) /2 width=3 by ex2_intro/ #H2L
@(fsle_frees_trans_eq … H2L … Hf1) /3 width=4 by sex_fwd_length, sym_eq/
qed-.

lemma frees_sex_conf_fsle (R):
      rex_fsle_compatible R →
      ∀L1,T,f1. L1 ⊢ 𝐅+❨T❩ ≘ f1 →
      ∀L2. L1 ⪤[cext2 R,cfull,f1] L2 →
      ∃∃f2. L2 ⊢ 𝐅+❨T❩ ≘ f2 & f1 ⊆ f2.
#R #HR #L1 #T #f1 #Hf1 #L2 #H1L
lapply (HR L1 L2 T ?) /2 width=3 by ex2_intro/ #H2L
@(fsle_frees_conf_eq … H2L … Hf1) /3 width=4 by sex_fwd_length, sym_eq/
qed-.

(* Properties with free variables inclusion for restricted closures *********)

(* Note: we just need lveq_inv_refl: ∀L, n1, n2. L ≋ⓧ*[n1, n2] L → ∧∧ 0 = n1 & 0 = n2 *)
lemma fsge_rex_trans (R):
      ∀L1,T1,T2. ❨L1,T1❩ ⊆ ❨L1,T2❩ →
      ∀L2. L1 ⪤[R,T2] L2 → L1 ⪤[R,T1] L2.
#R #L1 #T1 #T2 * #n1 #n2 #f1 #f2 #Hf1 #Hf2 #Hn #Hf #L2 #HL12
elim (lveq_inj_length … Hn ?) // #H1 #H2 destruct
/4 width=5 by rex_inv_frees, sle_sex_trans, ex2_intro/
qed-.

lemma rex_sym (R):
      rex_fsge_compatible R →
      (∀L1,L2,T1,T2. R L1 T1 T2 → R L2 T2 T1) →
      ∀T. symmetric … (rex R T).
#R #H1R #H2R #T #L1 #L2
* #f1 #Hf1 #HL12
elim (frees_sex_conf_fsge … Hf1 … HL12) -Hf1 //
/5 width=5 by sle_sex_trans, sex_sym, cext2_sym, ex2_intro/
qed-.

lemma rex_pair_sn_split (R1) (R2):
      (∀L. reflexive … (R1 L)) → (∀L. reflexive … (R2 L)) →
      rex_fsge_compatible R1 →
      ∀L1,L2,V. L1 ⪤[R1,V] L2 → ∀I,T.
      ∃∃L. L1 ⪤[R1,②[I]V.T] L & L ⪤[R2,V] L2.
#R1 #R2 #HR1 #HR2 #HR #L1 #L2 #V * #f #Hf #HL12 * [ #p ] #I #T
[ elim (frees_total L1 (ⓑ[p,I]V.T)) #g #Hg
  elim (frees_inv_bind … Hg) #y1 #y2 #H #_ #Hy
| elim (frees_total L1 (ⓕ[I]V.T)) #g #Hg
  elim (frees_inv_flat … Hg) #y1 #y2 #H #_ #Hy
]
lapply(frees_mono … H … Hf) -H #H1
lapply (pr_sor_eq_repl_back_sn … Hy … H1) -y1 #Hy
lapply (pr_sor_inv_sle_sn … Hy) -y2 #Hfg
elim (sex_sle_split_sn (cext2 R1) (cext2 R2) … HL12 … Hfg) -HL12 /2 width=1 by ext2_refl/ #L #HL1 #HL2
lapply (sle_sex_trans … HL1 … Hfg) // #H
elim (frees_sex_conf_fsge … Hf … H) -Hf -H
/4 width=7 by sle_sex_trans, ex2_intro/
qed-.

lemma rex_flat_dx_split (R1) (R2):
      (∀L. reflexive … (R1 L)) → (∀L. reflexive … (R2 L)) →
      rex_fsge_compatible R1 →
      ∀L1,L2,T. L1 ⪤[R1,T] L2 → ∀I,V.
      ∃∃L. L1 ⪤[R1,ⓕ[I]V.T] L & L ⪤[R2,T] L2.
#R1 #R2 #HR1 #HR2 #HR #L1 #L2 #T * #f #Hf #HL12 #I #V
elim (frees_total L1 (ⓕ[I]V.T)) #g #Hg
elim (frees_inv_flat … Hg) #y1 #y2 #_ #H #Hy
lapply(frees_mono … H … Hf) -H #H2
lapply (pr_sor_eq_repl_back_dx … Hy … H2) -y2 #Hy
lapply (pr_sor_inv_sle_dx … Hy) -y1 #Hfg
elim (sex_sle_split_sn (cext2 R1) (cext2 R2) … HL12 … Hfg) -HL12 /2 width=1 by ext2_refl/ #L #HL1 #HL2
lapply (sle_sex_trans … HL1 … Hfg) // #H
elim (frees_sex_conf_fsge … Hf … H) -Hf -H
/4 width=7 by sle_sex_trans, ex2_intro/
qed-.

lemma rex_bind_dx_split (R1) (R2):
      (∀L. reflexive … (R1 L)) → (∀L. reflexive … (R2 L)) →
      rex_fsge_compatible R1 →
      ∀I,L1,L2,V1,T. L1.ⓑ[I]V1 ⪤[R1,T] L2 → ∀p.
      ∃∃L,V. L1 ⪤[R1,ⓑ[p,I]V1.T] L & L.ⓑ[I]V ⪤[R2,T] L2 & R1 L1 V1 V.
#R1 #R2 #HR1 #HR2 #HR #I #L1 #L2 #V1 #T * #f #Hf #HL12 #p
elim (frees_total L1 (ⓑ[p,I]V1.T)) #g #Hg
elim (frees_inv_bind … Hg) #y1 #y2 #_ #H #Hy
lapply(frees_mono … H … Hf) -H #H2
lapply (pr_tl_eq_repl … H2) -H2 #H2
lapply (pr_sor_eq_repl_back_dx … Hy … H2) -y2 #Hy
lapply (pr_sor_inv_sle_dx … Hy) -y1 #Hfg
lapply (pr_sle_inv_tl_sn … Hfg) -Hfg #Hfg
elim (sex_sle_split_sn (cext2 R1) (cext2 R2) … HL12 … Hfg) -HL12 /2 width=1 by ext2_refl/ #Y #H #HL2
lapply (sle_sex_trans … H … Hfg) // #H0
elim (sex_inv_next1 … H) -H #Z #L #HL1 #H
elim (ext2_inv_pair_sn … H) -H #V #HV #H1 #H2 destruct
elim (frees_sex_conf_fsge … Hf … H0) -Hf -H0
/4 width=7 by sle_sex_trans, ex3_2_intro, ex2_intro/
qed-.

lemma rex_bind_dx_split_void (R1) (R2):
      (∀L. reflexive … (R1 L)) → (∀L. reflexive … (R2 L)) →
      rex_fsge_compatible R1 →
      ∀L1,L2,T. L1.ⓧ ⪤[R1,T] L2 → ∀p,I,V.
      ∃∃L. L1 ⪤[R1,ⓑ[p,I]V.T] L & L.ⓧ ⪤[R2,T] L2.
#R1 #R2 #HR1 #HR2 #HR #L1 #L2 #T * #f #Hf #HL12 #p #I #V
elim (frees_total L1 (ⓑ[p,I]V.T)) #g #Hg
elim (frees_inv_bind_void … Hg) #y1 #y2 #_ #H #Hy
lapply(frees_mono … H … Hf) -H #H2
lapply (pr_tl_eq_repl … H2) -H2 #H2
lapply (pr_sor_eq_repl_back_dx … Hy … H2) -y2 #Hy
lapply (pr_sor_inv_sle_dx … Hy) -y1 #Hfg
lapply (pr_sle_inv_tl_sn … Hfg) -Hfg #Hfg
elim (sex_sle_split_sn (cext2 R1) (cext2 R2) … HL12 … Hfg) -HL12 /2 width=1 by ext2_refl/ #Y #H #HL2
lapply (sle_sex_trans … H … Hfg) // #H0
elim (sex_inv_next1 … H) -H #Z #L #HL1 #H
elim (ext2_inv_unit_sn … H) -H #H destruct
elim (frees_sex_conf_fsge … Hf … H0) -Hf -H0
/4 width=7 by sle_sex_trans, ex2_intro/ (* note: 2 ex2_intro *)
qed-.

(* Main properties with free variables inclusion for restricted closures ****)

theorem rex_conf1 (R1) (R2):
        rex_fsge_compatible R2 → (c_reflexive … R2) →
        R_replace3_rex R1 R2 R1 R2 →
        ∀T. confluent1 … (rex R1 T) (rex R2 T).
#R1 #R2 #H1R #H2R #H3R #T #L1 #L * #f1 #Hf1 #HL1 #L2 * #f2 #Hf2 #HL12
lapply (frees_mono … Hf1 … Hf2) -Hf1 #Hf12
lapply (sex_eq_repl_back … HL1 … Hf12) -f1 #HL1
elim (frees_sex_conf_fsge … Hf2 … HL12) // #g2 #Hg2 #Hfg2
lapply (sex_repl … HL1 … HL12 L ?) //
[ /3 width=1 by sex_refl, ext2_refl/
| -g2 #g2 * #I1 [| #V1 ] #K1 #n #HLK1 #Hgf2 #Z1 #H1 #Z2 #H2 #Y1 #HY1 #Y2 #HY2 #Z #HZ
  [ lapply (ext2_inv_unit_sn … H1) -H1 #H destruct
    lapply (ext2_inv_unit_sn … H2) -H2 #H destruct
    lapply (ext2_inv_unit_sn … HZ) -HZ #H destruct
    /2 width=1 by ext2_unit/
  | elim (ext2_inv_pair_sn … H1) -H1 #W1 #HW1 #H destruct
    elim (ext2_inv_pair_sn … H2) -H2 #W2 #HW2 #H destruct
    elim (ext2_inv_pair_sn … HZ) -HZ #W #HW #H destruct
    elim (frees_inv_drops_next … Hf2 … HLK1 … Hgf2) -Hf2 -HLK1 -Hgf2 #g0 #Hg0 #Hg02
    lapply (sle_sex_trans … HY1 … Hg02) // -HY1 #HY1
    lapply (sle_sex_trans … HY2 … Hg02) // -HY2 #HY2
    /4 width=9 by ext2_pair, ex2_intro/
  ]
| /3 width=5 by sle_sex_trans, ex2_intro/
]
qed-.

theorem rex_conf (R1) (R2):
        rex_fsge_compatible R1 → rex_fsge_compatible R2 →
        R_confluent2_rex R1 R2 R1 R2 →
        ∀T. confluent2 … (rex R1 T) (rex R2 T).
#R1 #R2 #HR1 #HR2 #HR12 #T #L0 #L1 * #f1 #Hf1 #HL01 #L2 * #f #Hf #HL02
lapply (frees_mono … Hf1 … Hf) -Hf1 #Hf12
lapply (sex_eq_repl_back … HL01 … Hf12) -f1 #HL01
elim (sex_conf … HL01 … HL02) /2 width=3 by ex2_intro/ [ | -HL01 -HL02 ]
[ #L #HL1 #HL2
  elim (frees_sex_conf_fsge … Hf … HL01) // -HR1 -HL01 #f1 #Hf1 #H1
  elim (frees_sex_conf_fsge … Hf … HL02) // -HR2 -HL02 #f2 #Hf2 #H2
  lapply (sle_sex_trans … HL1 … H1) // -HL1 -H1 #HL1
  lapply (sle_sex_trans … HL2 … H2) // -HL2 -H2 #HL2
  /3 width=5 by ex2_intro/
| #g * #I0 [| #V0 ] #K0 #n #HLK0 #Hgf #Z1 #H1 #Z2 #H2 #K1 #HK01 #K2 #HK02
  [ lapply (ext2_inv_unit_sn … H1) -H1 #H destruct
    lapply (ext2_inv_unit_sn … H2) -H2 #H destruct
    /3 width=3 by ext2_unit, ex2_intro/
  | elim (ext2_inv_pair_sn … H1) -H1 #V1 #HV01 #H destruct
    elim (ext2_inv_pair_sn … H2) -H2 #V2 #HV02 #H destruct
    elim (frees_inv_drops_next … Hf … HLK0 … Hgf) -Hf -HLK0 -Hgf #g0 #Hg0 #H0
    lapply (sle_sex_trans … HK01 … H0) // -HK01 #HK01
    lapply (sle_sex_trans … HK02 … H0) // -HK02 #HK02
    elim (HR12 … HV01 … HV02 K1 … K2) /3 width=3 by ext2_pair, ex2_intro/
  ]
]
qed-.

theorem rex_trans_fsle (R1) (R2) (R3):
        rex_fsle_compatible R1 → f_transitive_next R1 R2 R3 →
        ∀L1,L,T. L1 ⪤[R1,T] L → ∀L2. L ⪤[R2,T] L2 → L1 ⪤[R3,T] L2.
#R1 #R2 #R3 #H1R #H2R #L1 #L #T #H
lapply (H1R … H) -H1R #H0
cases H -H #f1 #Hf1 #HL1 #L2 * #f2 #Hf2 #HL2
lapply (fsle_inv_frees_eq … H0 … Hf1 … Hf2) -H0 -Hf2
/4 width=14 by sex_trans_gen, sex_fwd_length, sle_sex_trans, ex2_intro/
qed-.

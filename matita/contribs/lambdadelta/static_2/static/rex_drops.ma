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

include "static_2/relocation/drops_cext2.ma".
include "static_2/relocation/drops_sex.ma".
include "static_2/static/frees_drops.ma".
include "static_2/static/rex.ma".

(* GENERIC EXTENSION ON REFERRED ENTRIES OF A CONTEXT-SENSITIVE REALTION ****)

definition f_dedropable_sn: predicate (relation3 lenv term term) ≝
                            λR. ∀b,f,L1,K1. ⬇*[b,f] L1 ≘ K1 →
                            ∀K2,T. K1 ⪤[R,T] K2 → ∀U. ⬆*[f] T ≘ U →
                            ∃∃L2. L1 ⪤[R,U] L2 & ⬇*[b,f] L2 ≘ K2 & L1 ≡[f] L2.

definition f_dropable_sn: predicate (relation3 lenv term term) ≝
                          λR. ∀b,f,L1,K1. ⬇*[b,f] L1 ≘ K1 → 𝐔⦃f⦄ →
                          ∀L2,U. L1 ⪤[R,U] L2 → ∀T. ⬆*[f] T ≘ U →
                          ∃∃K2. K1 ⪤[R,T] K2 & ⬇*[b,f] L2 ≘ K2.

definition f_dropable_dx: predicate (relation3 lenv term term) ≝
                          λR. ∀L1,L2,U. L1 ⪤[R,U] L2 →
                          ∀b,f,K2. ⬇*[b,f] L2 ≘ K2 → 𝐔⦃f⦄ → ∀T. ⬆*[f] T ≘ U →
                          ∃∃K1. ⬇*[b,f] L1 ≘ K1 & K1 ⪤[R,T] K2.

definition f_transitive_next: relation3 … ≝ λR1,R2,R3.
                              ∀f,L,T. L ⊢ 𝐅*⦃T⦄ ≘ f →
                              ∀g,I,K,n. ⬇*[n] L ≘ K.ⓘ{I} → ↑g = ⫱*[n] f →
                              sex_transitive (cext2 R1) (cext2 R2) (cext2 R3) (cext2 R1) cfull g K I.

(* Properties with generic slicing for local environments *******************)

lemma rex_liftable_dedropable_sn: ∀R. (∀L. reflexive ? (R L)) →
                                  d_liftable2_sn … lifts R → f_dedropable_sn R.
#R #H1R #H2R #b #f #L1 #K1 #HLK1 #K2 #T * #f1 #Hf1 #HK12 #U #HTU
elim (frees_total L1 U) #f2 #Hf2
lapply (frees_fwd_coafter … Hf2 … HLK1 … HTU … Hf1) -HTU #Hf
elim (sex_liftable_co_dedropable_sn … HLK1 … HK12 … Hf) -f1 -K1
/3 width=6 by cext2_d_liftable2_sn, cfull_lift_sn, ext2_refl, ex3_intro, ex2_intro/
qed-.

lemma rex_trans_next: ∀R1,R2,R3. rex_transitive R1 R2 R3 → f_transitive_next R1 R2 R3.
#R1 #R2 #R3 #HR #f #L1 #T #Hf #g #I1 #K1 #n #HLK #Hgf #I #H
generalize in match HLK; -HLK elim H -I1 -I
[ #I #_ #L2 #_ #I2 #H
  lapply (ext2_inv_unit_sn … H) -H #H destruct
  /2 width=1 by ext2_unit/
| #I #V1 #V #HV1 #HLK1 #L2 #HL12 #I2 #H
  elim (ext2_inv_pair_sn … H) -H #V2 #HV2 #H destruct
  elim (frees_inv_drops_next … Hf … HLK1 … Hgf) -f -HLK1 #f #Hf #Hfg
  /5 width=5 by ext2_pair, sle_sex_trans, ex2_intro/
]
qed.

(* Inversion lemmas with generic slicing for local environments *************)

(* Basic_2A1: uses: llpx_sn_inv_lift_le llpx_sn_inv_lift_be llpx_sn_inv_lift_ge *)
(* Basic_2A1: was: llpx_sn_drop_conf_O *)
lemma rex_dropable_sn: ∀R. f_dropable_sn R.
#R #b #f #L1 #K1 #HLK1 #H1f #L2 #U * #f2 #Hf2 #HL12 #T #HTU
elim (frees_total K1 T) #f1 #Hf1
lapply (frees_fwd_coafter … Hf2 … HLK1 … HTU … Hf1) -HTU #H2f
elim (sex_co_dropable_sn … HLK1 … HL12 … H2f) -f2 -L1
/3 width=3 by ex2_intro/
qed-.

(* Basic_2A1: was: llpx_sn_drop_trans_O *)
(* Note: the proof might be simplified *)
lemma rex_dropable_dx: ∀R. f_dropable_dx R.
#R #L1 #L2 #U * #f2 #Hf2 #HL12 #b #f #K2 #HLK2 #H1f #T #HTU
elim (drops_isuni_ex … H1f L1) #K1 #HLK1
elim (frees_total K1 T) #f1 #Hf1
lapply (frees_fwd_coafter … Hf2 … HLK1 … HTU … Hf1) -K1 #H2f
elim (sex_co_dropable_dx … HL12 … HLK2 … H2f) -L2
/4 width=9 by frees_inv_lifts, ex2_intro/
qed-.

(* Basic_2A1: uses: llpx_sn_inv_lift_O *)
lemma rex_inv_lifts_bi: ∀R,L1,L2,U. L1 ⪤[R,U] L2 → ∀b,f. 𝐔⦃f⦄ → 
                        ∀K1,K2. ⬇*[b,f] L1 ≘ K1 → ⬇*[b,f] L2 ≘ K2 →
                        ∀T. ⬆*[f] T ≘ U → K1 ⪤[R,T] K2.
#R #L1 #L2 #U #HL12 #b #f #Hf #K1 #K2 #HLK1 #HLK2 #T #HTU
elim (rex_dropable_sn … HLK1 … HL12 … HTU) -L1 -U // #Y #HK12 #HY
lapply (drops_mono … HY … HLK2) -b -f -L2 #H destruct //
qed-.

lemma rex_inv_lref_pair_sn: ∀R,L1,L2,i. L1 ⪤[R,#i] L2 → ∀I,K1,V1. ⬇*[i] L1 ≘ K1.ⓑ{I}V1 →
                            ∃∃K2,V2. ⬇*[i] L2 ≘ K2.ⓑ{I}V2 & K1 ⪤[R,V1] K2 & R K1 V1 V2.
#R #L1 #L2 #i #HL12 #I #K1 #V1 #HLK1 elim (rex_dropable_sn … HLK1 … HL12 (#0)) -HLK1 -HL12 //
#Y #HY #HLK2 elim (rex_inv_zero_pair_sn … HY) -HY
#K2 #V2 #HK12 #HV12 #H destruct /2 width=5 by ex3_2_intro/
qed-.

lemma rex_inv_lref_pair_dx: ∀R,L1,L2,i. L1 ⪤[R,#i] L2 → ∀I,K2,V2. ⬇*[i] L2 ≘ K2.ⓑ{I}V2 →
                            ∃∃K1,V1. ⬇*[i] L1 ≘ K1.ⓑ{I}V1 & K1 ⪤[R,V1] K2 & R K1 V1 V2.
#R #L1 #L2 #i #HL12 #I #K2 #V2 #HLK2 elim (rex_dropable_dx … HL12 … HLK2 … (#0)) -HLK2 -HL12 //
#Y #HLK1 #HY elim (rex_inv_zero_pair_dx … HY) -HY
#K1 #V1 #HK12 #HV12 #H destruct /2 width=5 by ex3_2_intro/
qed-.

lemma rex_inv_lref_pair_bi (R) (L1) (L2) (i):
                           L1 ⪤[R,#i] L2 →
                           ∀I1,K1,V1. ⬇*[i] L1 ≘ K1.ⓑ{I1}V1 →
                           ∀I2,K2,V2. ⬇*[i] L2 ≘ K2.ⓑ{I2}V2 →
                           ∧∧ K1 ⪤[R,V1] K2 & R K1 V1 V2 & I1 = I2.
#R #L1 #L2 #i #H12 #I1 #K1 #V1 #H1 #I2 #K2 #V2 #H2
elim (rex_inv_lref_pair_sn … H12 … H1) -L1 #Y2 #X2 #HLY2 #HK12 #HV12
lapply (drops_mono … HLY2 … H2) -HLY2 -H2 #H destruct
/2 width=1 by and3_intro/
qed-.

lemma rex_inv_lref_unit_sn: ∀R,L1,L2,i. L1 ⪤[R,#i] L2 → ∀I,K1. ⬇*[i] L1 ≘ K1.ⓤ{I} →
                            ∃∃f,K2. ⬇*[i] L2 ≘ K2.ⓤ{I} & K1 ⪤[cext2 R,cfull,f] K2 & 𝐈⦃f⦄.
#R #L1 #L2 #i #HL12 #I #K1 #HLK1 elim (rex_dropable_sn … HLK1 … HL12 (#0)) -HLK1 -HL12 //
#Y #HY #HLK2 elim (rex_inv_zero_unit_sn … HY) -HY
#f #K2 #Hf #HK12 #H destruct /2 width=5 by ex3_2_intro/
qed-.

lemma rex_inv_lref_unit_dx: ∀R,L1,L2,i. L1 ⪤[R,#i] L2 → ∀I,K2. ⬇*[i] L2 ≘ K2.ⓤ{I} →
                            ∃∃f,K1. ⬇*[i] L1 ≘ K1.ⓤ{I} & K1 ⪤[cext2 R,cfull,f] K2 & 𝐈⦃f⦄.
#R #L1 #L2 #i #HL12 #I #K2 #HLK2 elim (rex_dropable_dx … HL12 … HLK2 … (#0)) -HLK2 -HL12 //
#Y #HLK1 #HY elim (rex_inv_zero_unit_dx … HY) -HY
#f #K2 #Hf #HK12 #H destruct /2 width=5 by ex3_2_intro/
qed-.

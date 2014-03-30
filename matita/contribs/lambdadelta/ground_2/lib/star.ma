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

include "basics/star1.ma".
include "ground_2/xoa/xoa_props.ma".

(* PROPERTIES OF RELATIONS **************************************************)

definition Decidable: Prop → Prop ≝ λR. R ∨ (R → ⊥).

definition Transitive: ∀A. ∀R: relation A. Prop ≝ λA,R.
                       ∀a1,a0. R a1 a0 → ∀a2. R a0 a2 → R a1 a2.

definition confluent2: ∀A. ∀R1,R2: relation A. Prop ≝ λA,R1,R2.
                       ∀a0,a1. R1 a0 a1 → ∀a2. R2 a0 a2 →
                       ∃∃a. R2 a1 a & R1 a2 a.

definition transitive2: ∀A. ∀R1,R2: relation A. Prop ≝ λA,R1,R2.
                        ∀a1,a0. R1 a1 a0 → ∀a2. R2 a0 a2 →
                        ∃∃a. R2 a1 a & R1 a a2.

definition bi_confluent:  ∀A,B. ∀R: bi_relation A B. Prop ≝ λA,B,R.
                          ∀a0,a1,b0,b1. R a0 b0 a1 b1 → ∀a2,b2. R a0 b0 a2 b2 →
                          ∃∃a,b. R a1 b1 a b & R a2 b2 a b.

definition LTC: ∀A:Type[0]. ∀B. (A→relation B) → (A→relation B) ≝
                λA,B,R,a. TC … (R a).

definition lsub_trans: ∀A,B. relation2 (A→relation B) (relation A) ≝ λA,B,R1,R2.
                       ∀L2,T1,T2. R1 L2 T1 T2 → ∀L1. R2 L1 L2 → R1 L1 T1 T2.

definition s_r_transitive: ∀A,B. relation2 (A→relation B) (B→relation A) ≝ λA,B,R1,R2.
                           ∀L2,T1,T2. R1 L2 T1 T2 → ∀L1. R2 T1 L1 L2 → LTC … R1 L1 T1 T2.

definition s_rs_transitive: ∀A,B. relation2 (A→relation B) (B→relation A) ≝ λA,B,R1,R2.
                            ∀L2,T1,T2. LTC … R1 L2 T1 T2 → ∀L1. R2 T1 L1 L2 → LTC … R1 L1 T1 T2.

definition s_r_confluent1: ∀A,B. relation2 (A→relation B) (B→relation A) ≝ λA,B,R1,R2.
                           ∀L1,T1,T2. R1 L1 T1 T2 → ∀L2. R2 T1 L1 L2 → R2 T2 L1 L2.

lemma TC_strip1: ∀A,R1,R2. confluent2 A R1 R2 →
                 ∀a0,a1. TC … R1 a0 a1 → ∀a2. R2 a0 a2 →
                 ∃∃a. R2 a1 a & TC … R1 a2 a.
#A #R1 #R2 #HR12 #a0 #a1 #H elim H -a1
[ #a1 #Ha01 #a2 #Ha02
  elim (HR12 … Ha01 … Ha02) -HR12 -a0 /3 width=3 by inj, ex2_intro/
| #a #a1 #_ #Ha1 #IHa0 #a2 #Ha02
  elim (IHa0 … Ha02) -a0 #a0 #Ha0 #Ha20
  elim (HR12 … Ha1 … Ha0) -HR12 -a /4 width=5 by step, ex2_intro/
]
qed.

lemma TC_strip2: ∀A,R1,R2. confluent2 A R1 R2 →
                 ∀a0,a2. TC … R2 a0 a2 → ∀a1. R1 a0 a1 →
                 ∃∃a. TC … R2 a1 a & R1 a2 a.
#A #R1 #R2 #HR12 #a0 #a2 #H elim H -a2
[ #a2 #Ha02 #a1 #Ha01
  elim (HR12 … Ha01 … Ha02) -HR12 -a0 /3 width=3 by inj, ex2_intro/
| #a #a2 #_ #Ha2 #IHa0 #a1 #Ha01
  elim (IHa0 … Ha01) -a0 #a0 #Ha10 #Ha0
  elim (HR12 … Ha0 … Ha2) -HR12 -a /4 width=3 by step, ex2_intro/
]
qed.

lemma TC_confluent2: ∀A,R1,R2.
                     confluent2 A R1 R2 → confluent2 A (TC … R1) (TC … R2).
#A #R1 #R2 #HR12 #a0 #a1 #H elim H -a1
[ #a1 #Ha01 #a2 #Ha02
  elim (TC_strip2 … HR12 … Ha02 … Ha01) -HR12 -a0 /3 width=3 by inj, ex2_intro/
| #a #a1 #_ #Ha1 #IHa0 #a2 #Ha02
  elim (IHa0 … Ha02) -a0 #a0 #Ha0 #Ha20
  elim (TC_strip2 … HR12 … Ha0 … Ha1) -HR12 -a /4 width=5 by step, ex2_intro/
]
qed.

lemma TC_strap1: ∀A,R1,R2. transitive2 A R1 R2 →
                 ∀a1,a0. TC … R1 a1 a0 → ∀a2. R2 a0 a2 →
                 ∃∃a. R2 a1 a & TC … R1 a a2.
#A #R1 #R2 #HR12 #a1 #a0 #H elim H -a0
[ #a0 #Ha10 #a2 #Ha02
  elim (HR12 … Ha10 … Ha02) -HR12 -a0 /3 width=3 by inj, ex2_intro/
| #a #a0 #_ #Ha0 #IHa #a2 #Ha02
  elim (HR12 … Ha0 … Ha02) -HR12 -a0 #a0 #Ha0 #Ha02
  elim (IHa … Ha0) -a /4 width=5 by step, ex2_intro/
]
qed.

lemma TC_strap2: ∀A,R1,R2. transitive2 A R1 R2 →
                 ∀a0,a2. TC … R2 a0 a2 → ∀a1. R1 a1 a0 →
                 ∃∃a. TC … R2 a1 a & R1 a a2.
#A #R1 #R2 #HR12 #a0 #a2 #H elim H -a2
[ #a2 #Ha02 #a1 #Ha10
  elim (HR12 … Ha10 … Ha02) -HR12 -a0 /3 width=3 by inj, ex2_intro/
| #a #a2 #_ #Ha02 #IHa #a1 #Ha10
  elim (IHa … Ha10) -a0 #a0 #Ha10 #Ha0
  elim (HR12 … Ha0 … Ha02) -HR12 -a /4 width=3 by step, ex2_intro/
]
qed.

lemma TC_transitive2: ∀A,R1,R2.
                      transitive2 A R1 R2 → transitive2 A (TC … R1) (TC … R2).
#A #R1 #R2 #HR12 #a1 #a0 #H elim H -a0
[ #a0 #Ha10 #a2 #Ha02
  elim (TC_strap2 … HR12 … Ha02 … Ha10) -HR12 -a0 /3 width=3 by inj, ex2_intro/
| #a #a0 #_ #Ha0 #IHa #a2 #Ha02
  elim (TC_strap2 … HR12 … Ha02 … Ha0) -HR12 -a0 #a0 #Ha0 #Ha02
  elim (IHa … Ha0) -a /4 width=5 by step, ex2_intro/
]
qed.

definition NF: ∀A. relation A → relation A → predicate A ≝
   λA,R,S,a1. ∀a2. R a1 a2 → S a2 a1.

definition NF_dec: ∀A. relation A → relation A → Prop ≝
                   λA,R,S. ∀a1. NF A R S a1 ∨
                   ∃∃a2. R … a1 a2 & (S a2 a1 → ⊥).

inductive SN (A) (R,S:relation A): predicate A ≝
| SN_intro: ∀a1. (∀a2. R a1 a2 → (S a2 a1 → ⊥) → SN A R S a2) → SN A R S a1
.

lemma NF_to_SN: ∀A,R,S,a. NF A R S a → SN A R S a.
#A #R #S #a1 #Ha1
@SN_intro #a2 #HRa12 #HSa12
elim HSa12 -HSa12 /2 width=1 by/
qed.

lemma SN_to_NF: ∀A,R,S. NF_dec A R S →
                ∀a1. SN A R S a1 →
                ∃∃a2. star … R a1 a2 & NF A R S a2.
#A #R #S #HRS #a1 #H elim H -a1
#a1 #_ #IHa1 elim (HRS a1) -HRS /2 width=3 by srefl, ex2_intro/
* #a0 #Ha10 #Ha01 elim (IHa1 … Ha10 Ha01) -IHa1 -Ha01 /3 width=3 by star_compl, ex2_intro/
qed-.

definition NF_sn: ∀A. relation A → relation A → predicate A ≝
   λA,R,S,a2. ∀a1. R a1 a2 → S a2 a1.

inductive SN_sn (A) (R,S:relation A): predicate A ≝
| SN_sn_intro: ∀a2. (∀a1. R a1 a2 → (S a2 a1 → ⊥) → SN_sn A R S a1) → SN_sn A R S a2
.

lemma NF_to_SN_sn: ∀A,R,S,a. NF_sn A R S a → SN_sn A R S a.
#A #R #S #a2 #Ha2
@SN_sn_intro #a1 #HRa12 #HSa12
elim HSa12 -HSa12 /2 width=1 by/
qed.

lemma LTC_lsub_trans: ∀A,B,R,S. lsub_trans A B R S → lsub_trans A B (LTC … R) S.
#A #B #R #S #HRS #L2 #T1 #T2 #H elim H -T2 /3 width=3 by inj/
#T #T2 #_ #HT2 #IHT1 #L1 #HL12
lapply (HRS … HT2 … HL12) -HRS -HT2 /3 width=3 by step/
qed-.

lemma s_r_conf1_LTC1: ∀A,B,S,R. s_r_confluent1 A B S R → s_r_confluent1 A B (LTC … S) R.
#A #B #S #R #HSR #L1 #T1 #T2 #H @(TC_ind_dx … T1 H) -T1 /3 width=3 by/
qed-.

lemma s_r_trans_LTC1: ∀A,B,S,R. s_r_confluent1 A B S R →
                      s_r_transitive A B S R → s_rs_transitive A B S R.
#A #B #S #R #H1SR #H2SR #L2 #T1 #T2 #H @(TC_ind_dx … T1 H) -T1 /2 width=3 by/
#T1 #T #HT1 #_ #IHT2 #L1 #HL12 lapply (H2SR … HT1 … HL12) -H2SR -HT1
/4 width=5 by s_r_conf1_LTC1, trans_TC/
qed-.

lemma s_r_trans_LTC2: ∀A,B,S,R. s_rs_transitive A B S R → s_r_transitive A B S (LTC … R).
#A #B #S #R #HSR #L2 #T1 #T2 #HT12 #L1 #H @(TC_ind_dx … L1 H) -L1 /3 width=3 by inj/
qed-.

lemma s_r_to_s_rs_trans: ∀A,B,S,R. s_r_transitive A B (LTC … S) R →
                         s_rs_transitive A B S R.
#A #B #S #R #HSR #L2 #T1 #T2 #HL2 #L1 #HT1
elim (TC_idem … (S L1) …  T1 T2)
#_ #H @H @HSR //
qed-.

lemma s_rs_to_s_r_trans: ∀A,B,S,R. s_rs_transitive A B S R →
                         s_r_transitive A B (LTC … S) R.
#A #B #S #R #HSR #L2 #T1 #T2 #HL2 #L1 #HT1
elim (TC_idem … (S L1) …  T1 T2)
#H #_ @H @HSR //
qed-.

lemma s_rs_trans_TC1: ∀A,B,S,R. s_rs_transitive A B S R →
                      s_rs_transitive A B (LTC … S) R.
#A #B #S #R #HSR #L2 #T1 #T2 #HL2 #L1 #HT1
elim (TC_idem … (S L1) …  T1 T2)
elim (TC_idem … (S L2) …  T1 T2)
#_ #H1 #H2 #_ @H2 @HSR /3 width=3 by/
qed-.

(* relations on unboxed pairs ***********************************************)

lemma bi_TC_strip: ∀A,B,R. bi_confluent A B R →
                   ∀a0,a1,b0,b1. R a0 b0 a1 b1 → ∀a2,b2. bi_TC … R a0 b0 a2 b2 →
                   ∃∃a,b. bi_TC … R a1 b1 a b & R a2 b2 a b.
#A #B #R #HR #a0 #a1 #b0 #b1 #H01 #a2 #b2 #H elim H -a2 -b2
[ #a2 #b2 #H02
  elim (HR … H01 … H02) -HR -a0 -b0 /3 width=4 by ex2_2_intro, bi_inj/
| #a2 #b2 #a3 #b3 #_ #H23 * #a #b #H1 #H2
  elim (HR … H23 … H2) -HR -a0 -b0 -a2 -b2 /3 width=4 by ex2_2_intro, bi_step/
]
qed.

lemma bi_TC_confluent: ∀A,B,R. bi_confluent A B R →
                       bi_confluent A B (bi_TC … R).
#A #B #R #HR #a0 #a1 #b0 #b1 #H elim H -a1 -b1
[ #a1 #b1 #H01 #a2 #b2 #H02
  elim (bi_TC_strip … HR … H01 … H02) -a0 -b0 /3 width=4 by ex2_2_intro, bi_inj/
| #a1 #b1 #a3 #b3 #_ #H13 #IH #a2 #b2 #H02
  elim (IH … H02) -a0 -b0 #a0 #b0 #H10 #H20
  elim (bi_TC_strip … HR … H13 … H10) -a1 -b1 /3 width=7 by ex2_2_intro, bi_step/
]
qed.

lemma bi_TC_decomp_r: ∀A,B. ∀R:bi_relation A B.
                      ∀a1,a2,b1,b2. bi_TC … R a1 b1 a2 b2 →
                      R a1 b1 a2 b2 ∨
                      ∃∃a,b. bi_TC … R a1 b1 a b & R a b a2 b2.
#A #B #R #a1 #a2 #b1 #b2 * -a2 -b2 /2 width=1/ /3 width=4 by ex2_2_intro, or_intror/
qed-.

lemma bi_TC_decomp_l: ∀A,B. ∀R:bi_relation A B.
                      ∀a1,a2,b1,b2. bi_TC … R a1 b1 a2 b2 →
                      R a1 b1 a2 b2 ∨
                      ∃∃a,b. R a1 b1 a b & bi_TC … R a b a2 b2.
#A #B #R #a1 #a2 #b1 #b2 #H @(bi_TC_ind_dx … a1 b1 H) -a1 -b1
[ /2 width=1 by or_introl/
| #a1 #a #b1 #b #Hab1 #Hab2 #_ /3 width=4 by ex2_2_intro, or_intror/ (**) (* auto fails without #_ *)
]
qed-.

(* relations on unboxed triples *********************************************)

definition tri_RC: ∀A,B,C. tri_relation A B C → tri_relation A B C ≝
                   λA,B,C,R,a1,b1,c1,a2,b2,c2. R … a1 b1 c1 a2 b2 c2 ∨
                   ∧∧ a1 = a2 & b1 = b2 & c1 = c2.

lemma tri_RC_reflexive: ∀A,B,C,R. tri_reflexive A B C (tri_RC … R).
/3 width=1 by and3_intro, or_intror/ qed.

definition tri_star: ∀A,B,C,R. tri_relation A B C ≝
                     λA,B,C,R. tri_RC A B C (tri_TC … R).

lemma tri_star_tri_reflexive: ∀A,B,C,R. tri_reflexive A B C (tri_star … R).
/2 width=1 by/ qed.

lemma tri_TC_to_tri_star: ∀A,B,C,R,a1,b1,c1,a2,b2,c2.
                          tri_TC A B C R a1 b1 c1 a2 b2 c2 →
                          tri_star A B C R a1 b1 c1 a2 b2 c2.
/2 width=1 by or_introl/ qed.

lemma tri_R_to_tri_star: ∀A,B,C,R,a1,b1,c1,a2,b2,c2.
                         R a1 b1 c1 a2 b2 c2 → tri_star A B C R a1 b1 c1 a2 b2 c2.
/3 width=1 by tri_TC_to_tri_star, tri_inj/ qed.

lemma tri_star_strap1: ∀A,B,C,R,a1,a,a2,b1,b,b2,c1,c,c2.
                       tri_star A B C R a1 b1 c1 a b c →
                       R a b c a2 b2 c2 → tri_star A B C R a1 b1 c1 a2 b2 c2.
#A #B #C #R #a1 #a #a2 #b1 #b #b2 #c1 #c #c2 *
[ /3 width=5 by tri_TC_to_tri_star, tri_step/
| * #H1 #H2 #H3 destruct /2 width=1 by tri_R_to_tri_star/
]
qed.

lemma tri_star_strap2: ∀A,B,C,R,a1,a,a2,b1,b,b2,c1,c,c2. R a1 b1 c1 a b c →
                       tri_star A B C R a b c a2 b2 c2 →
                       tri_star A B C R a1 b1 c1 a2 b2 c2.
#A #B #C #R #a1 #a #a2 #b1 #b #b2 #c1 #c #c2 #H *
[ /3 width=5 by tri_TC_to_tri_star, tri_TC_strap/
| * #H1 #H2 #H3 destruct /2 width=1 by tri_R_to_tri_star/
]
qed.

lemma tri_star_to_tri_TC_to_tri_TC: ∀A,B,C,R,a1,a,a2,b1,b,b2,c1,c,c2.
                                    tri_star A B C R a1 b1 c1 a b c →
                                    tri_TC A B C R a b c a2 b2 c2 →
                                    tri_TC A B C R a1 b1 c1 a2 b2 c2.
#A #B #C #R #a1 #a #a2 #b1 #b #b2 #c1 #c #c2 *
[ /2 width=5 by tri_TC_transitive/
| * #H1 #H2 #H3 destruct /2 width=1 by/
]
qed.

lemma tri_TC_to_tri_star_to_tri_TC: ∀A,B,C,R,a1,a,a2,b1,b,b2,c1,c,c2.
                                    tri_TC A B C R a1 b1 c1 a b c →
                                    tri_star A B C R a b c a2 b2 c2 →
                                    tri_TC A B C R a1 b1 c1 a2 b2 c2.
#A #B #C #R #a1 #a #a2 #b1 #b #b2 #c1 #c #c2 #H *
[ /2 width=5 by tri_TC_transitive/
| * #H1 #H2 #H3 destruct /2 width=1 by/
]
qed.

lemma tri_tansitive_tri_star: ∀A,B,C,R. tri_transitive A B C (tri_star … R).
#A #B #C #R #a1 #a #b1 #b #c1 #c #H #a2 #b2 #c2 *
[ /3 width=5 by tri_star_to_tri_TC_to_tri_TC, tri_TC_to_tri_star/
| * #H1 #H2 #H3 destruct /2 width=1 by/
]
qed.

lemma tri_star_ind: ∀A,B,C,R,a1,b1,c1. ∀P:relation3 A B C. P a1 b1 c1 →
                    (∀a,a2,b,b2,c,c2. tri_star … R a1 b1 c1 a b c → R a b c a2 b2 c2 → P a b c → P a2 b2 c2) →
                    ∀a2,b2,c2. tri_star … R a1 b1 c1 a2 b2 c2 → P a2 b2 c2.
#A #B #C #R #a1 #b1 #c1 #P #H #IH #a2 #b2 #c2 *
[ #H12 elim H12 -a2 -b2 -c2 /3 width=6 by tri_TC_to_tri_star/
| * #H1 #H2 #H3 destruct //
]
qed-.

lemma tri_star_ind_dx: ∀A,B,C,R,a2,b2,c2. ∀P:relation3 A B C. P a2 b2 c2 →
                       (∀a1,a,b1,b,c1,c. R a1 b1 c1 a b c → tri_star … R a b c a2 b2 c2 → P a b c → P a1 b1 c1) →
                       ∀a1,b1,c1. tri_star … R a1 b1 c1 a2 b2 c2 → P a1 b1 c1.
#A #B #C #R #a2 #b2 #c2 #P #H #IH #a1 #b1 #c1 *
[ #H12 @(tri_TC_ind_dx … a1 b1 c1 H12) -a1 -b1 -c1 /3 width=6 by tri_TC_to_tri_star/
| * #H1 #H2 #H3 destruct //
]
qed-.

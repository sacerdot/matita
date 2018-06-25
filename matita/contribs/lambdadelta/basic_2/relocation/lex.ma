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

include "ground_2/pull/pull_2.ma".
include "ground_2/pull/pull_4.ma".
include "ground_2/relocation/rtmap_uni.ma".
include "basic_2/notation/relations/relation_3.ma".
include "basic_2/syntax/cext2.ma".
include "basic_2/relocation/sex.ma".

(* GENERIC EXTENSION OF A CONTEXT-SENSITIVE REALTION FOR TERMS **************)

definition lex (R): relation lenv ≝
                    λL1,L2. ∃∃f. 𝐈⦃f⦄ & L1 ⪤[cfull, cext2 R, f] L2.

interpretation "generic extension (local environment)"
   'Relation R L1 L2 = (lex R L1 L2).

definition lex_confluent: relation (relation3 …) ≝ λR1,R2.
                          ∀L0,T0,T1. R1 L0 T0 T1 → ∀T2. R2 L0 T0 T2 →
                          ∀L1. L0 ⪤[R1] L1 → ∀L2. L0 ⪤[R2] L2 →
                          ∃∃T. R2 L1 T1 T & R1 L2 T2 T.

definition lex_transitive: relation (relation3 …) ≝ λR1,R2.
                           ∀L1,T1,T. R1 L1 T1 T → ∀L2. L1 ⪤[R1] L2 →
                           ∀T2. R2 L2 T T2 → R1 L1 T1 T2.

(* Basic properties *********************************************************)

(* Basic_2A1: was: lpx_sn_atom *)
lemma lex_atom (R): ⋆ ⪤[R] ⋆.
/2 width=3 by sex_atom, ex2_intro/ qed.

lemma lex_bind (R): ∀I1,I2,K1,K2. K1 ⪤[R] K2 → cext2 R K1 I1 I2 →
                    K1.ⓘ{I1} ⪤[R] K2.ⓘ{I2}.
#R #I1 #I2 #K1 #K2 * #f #Hf #HK12 #HI12
/3 width=3 by sex_push, isid_push, ex2_intro/
qed.

(* Basic_2A1: was: lpx_sn_refl *)
lemma lex_refl (R): c_reflexive … R → reflexive … (lex R).
/4 width=3 by sex_refl, ext2_refl, ex2_intro/ qed.

lemma lex_co (R1) (R2): (∀L,T1,T2. R1 L T1 T2 → R2 L T1 T2) →
                        ∀L1,L2. L1 ⪤[R1] L2 → L1 ⪤[R2] L2.
#R1 #R2 #HR #L1 #L2 * /5 width=7 by sex_co, cext2_co, ex2_intro/
qed-.

(* Advanced properties ******************************************************)

lemma lex_bind_refl_dx (R): c_reflexive … R →
                            ∀I,K1,K2. K1 ⪤[R] K2 → K1.ⓘ{I} ⪤[R] K2.ⓘ{I}.
/3 width=3 by ext2_refl, lex_bind/ qed.

lemma lex_unit (R): ∀I,K1,K2. K1 ⪤[R] K2 → K1.ⓤ{I} ⪤[R] K2.ⓤ{I}.
/3 width=1 by lex_bind, ext2_unit/ qed.

(* Basic_2A1: was: lpx_sn_pair *)
lemma lex_pair (R): ∀I,K1,K2,V1,V2. K1 ⪤[R] K2 → R K1 V1 V2 →
                    K1.ⓑ{I}V1 ⪤[R] K2.ⓑ{I}V2.
/3 width=1 by lex_bind, ext2_pair/ qed.

(* Basic inversion lemmas ***************************************************)

(* Basic_2A1: was: lpx_sn_inv_atom1: *)
lemma lex_inv_atom_sn (R): ∀L2. ⋆ ⪤[R] L2 → L2 = ⋆.
#R #L2 * #f #Hf #H >(sex_inv_atom1 … H) -L2 //
qed-.

lemma lex_inv_bind_sn (R): ∀I1,L2,K1. K1.ⓘ{I1} ⪤[R] L2 →
                           ∃∃I2,K2. K1 ⪤[R] K2 & cext2 R K1 I1 I2 & L2 = K2.ⓘ{I2}.
#R #I1 #L2 #K1 * #f #Hf #H
lapply (sex_eq_repl_fwd … H (⫯f) ?) -H /2 width=1 by eq_push_inv_isid/ #H
elim (sex_inv_push1 … H) -H #I2 #K2 #HK12 #HI12 #H destruct
/3 width=5 by ex2_intro, ex3_2_intro/
qed-.

(* Basic_2A1: was: lpx_sn_inv_atom2 *)
lemma lex_inv_atom_dx (R): ∀L1. L1 ⪤[R] ⋆ → L1 = ⋆.
#R #L1 * #f #Hf #H >(sex_inv_atom2 … H) -L1 //
qed-.

lemma lex_inv_bind_dx (R): ∀I2,L1,K2. L1 ⪤[R] K2.ⓘ{I2} →
                           ∃∃I1,K1. K1 ⪤[R] K2 & cext2 R K1 I1 I2 & L1 = K1.ⓘ{I1}.
#R #I2 #L1 #K2 * #f #Hf #H
lapply (sex_eq_repl_fwd … H (⫯f) ?) -H /2 width=1 by eq_push_inv_isid/ #H
elim (sex_inv_push2 … H) -H #I1 #K1 #HK12 #HI12 #H destruct
/3 width=5 by ex3_2_intro, ex2_intro/
qed-.

(* Advanced inversion lemmas ************************************************)

lemma lex_inv_unit_sn (R): ∀I,L2,K1. K1.ⓤ{I} ⪤[R] L2 →
                           ∃∃K2. K1 ⪤[R] K2 & L2 = K2.ⓤ{I}.
#R #I #L2 #K1 #H
elim (lex_inv_bind_sn … H) -H #Z2 #K2 #HK12 #HZ2 #H destruct
elim (ext2_inv_unit_sn … HZ2) -HZ2
/2 width=3 by ex2_intro/
qed-.

(* Basic_2A1: was: lpx_sn_inv_pair1 *)
lemma lex_inv_pair_sn (R): ∀I,L2,K1,V1. K1.ⓑ{I}V1 ⪤[R] L2 →
                           ∃∃K2,V2. K1 ⪤[R] K2 & R K1 V1 V2 & L2 = K2.ⓑ{I}V2.
#R #I #L2 #K1 #V1 #H
elim (lex_inv_bind_sn … H) -H #Z2 #K2 #HK12 #HZ2 #H destruct
elim (ext2_inv_pair_sn … HZ2) -HZ2 #V2 #HV12 #H destruct
/2 width=5 by ex3_2_intro/
qed-.

lemma lex_inv_unit_dx (R): ∀I,L1,K2. L1 ⪤[R] K2.ⓤ{I} →
                           ∃∃K1. K1 ⪤[R] K2 & L1 = K1.ⓤ{I}.
#R #I #L1 #K2 #H
elim (lex_inv_bind_dx … H) -H #Z1 #K1 #HK12 #HZ1 #H destruct
elim (ext2_inv_unit_dx … HZ1) -HZ1
/2 width=3 by ex2_intro/
qed-.

(* Basic_2A1: was: lpx_sn_inv_pair2 *)
lemma lex_inv_pair_dx (R): ∀I,L1,K2,V2. L1 ⪤[R] K2.ⓑ{I}V2 →
                           ∃∃K1,V1. K1 ⪤[R] K2 & R K1 V1 V2 & L1 = K1.ⓑ{I}V1.
#R #I #L1 #K2 #V2 #H
elim (lex_inv_bind_dx … H) -H #Z1 #K1 #HK12 #HZ1 #H destruct
elim (ext2_inv_pair_dx … HZ1) -HZ1 #V1 #HV12 #H destruct
/2 width=5 by ex3_2_intro/
qed-.

(* Basic_2A1: was: lpx_sn_inv_pair *)
lemma lex_inv_pair (R): ∀I1,I2,L1,L2,V1,V2.
                        L1.ⓑ{I1}V1 ⪤[R] L2.ⓑ{I2}V2 →
                        ∧∧ L1 ⪤[R] L2 & R L1 V1 V2 & I1 = I2.
#R #I1 #I2 #L1 #L2 #V1 #V2 #H elim (lex_inv_pair_sn … H) -H
#L0 #V0 #HL10 #HV10 #H destruct /2 width=1 by and3_intro/
qed-.

(* Basic eliminators ********************************************************)

lemma lex_ind (R) (Q:relation2 …):
              Q (⋆) (⋆) →
              (
                 ∀I,K1,K2. K1 ⪤[R] K2 → Q K1 K2 → Q (K1.ⓤ{I}) (K2.ⓤ{I})
              ) → (
                 ∀I,K1,K2,V1,V2. K1 ⪤[R] K2 → Q K1 K2 → R K1 V1 V2 →Q (K1.ⓑ{I}V1) (K2.ⓑ{I}V2)
              ) →
              ∀L1,L2. L1 ⪤[R] L2 → Q L1 L2.
#R #Q #IH1 #IH2 #IH3 #L1 #L2 * #f @pull_2 #H
elim H -f -L1 -L2 // #f #I1 #I2 #K1 #K2 @pull_4 #H
[ elim (isid_inv_next … H)
| lapply (isid_inv_push … H ??)
] -H [5:|*: // ] #Hf @pull_2 #H
elim H -H /3 width=3 by ex2_intro/
qed-.

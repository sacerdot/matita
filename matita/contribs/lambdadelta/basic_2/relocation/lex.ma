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

include "ground_2/relocation/rtmap_uni.ma".
include "basic_2/notation/relations/relation_3.ma".
include "basic_2/syntax/cext2.ma".
include "basic_2/relocation/lexs.ma".

(* GENERIC EXTENSION OF A CONTEXT-SENSITIVE REALTION ON TERMS ***************)

(* Basic_2A1: includes: lpx_sn_atom lpx_sn_pair *)
definition lex: (lenv → relation term) → relation lenv ≝
                λR,L1,L2. ∃∃f. 𝐈⦃f⦄ & L1 ⪤*[cfull, cext2 R, f] L2.

interpretation "generic extension (local environment)"
   'Relation R L1 L2 = (lex R L1 L2).

(* Basic properties *********************************************************)

(* Basic_2A1: was: lpx_sn_refl *)
lemma lex_refl: ∀R. c_reflexive … R → reflexive … (lex R).
/4 width=3 by lexs_refl, ext2_refl, ex2_intro/ qed.

(* Basic inversion lemmas ***************************************************)

(* Basic_2A1: was: lpx_sn_inv_atom1: *)
lemma lex_inv_atom_sn: ∀R,L2. ⋆ ⪤[R] L2 → L2 = ⋆.
#R #L2 * #f #Hf #H >(lexs_inv_atom1 … H) -L2 //
qed-.

(* Basic_2A1: was: lpx_sn_inv_pair1 *)
lemma lex_inv_pair_sn: ∀R,I,L2,K1,V1. K1.ⓑ{I}V1 ⪤[R] L2 →
                       ∃∃K2,V2. K1 ⪤[R] K2 & R K1 V1 V2 & L2 = K2.ⓑ{I}V2.
#R #I #L2 #K1 #V1 * #f #Hf #H
lapply (lexs_eq_repl_fwd … H (↑f) ?) -H /2 width=1 by eq_push_inv_isid/ #H
elim (lexs_inv_push1 … H) -H #Z2 #K2 #HK12 #HZ2 #H destruct
elim (ext2_inv_pair_sn … HZ2) -HZ2 #V2 #HV12 #H destruct
/3 width=5 by ex3_2_intro, ex2_intro/
qed-.

(* Basic_2A1: was: lpx_sn_inv_atom2 *)
lemma lex_inv_atom_dx: ∀R,L1. L1 ⪤[R] ⋆ → L1 = ⋆.
#R #L1 * #f #Hf #H >(lexs_inv_atom2 … H) -L1 //
qed-.

(* Basic_2A1: was: lpx_sn_inv_pair2 *)
lemma lex_inv_pair_dx: ∀R,I,L1,K2,V2. L1 ⪤[R] K2.ⓑ{I}V2 →
                       ∃∃K1,V1. K1 ⪤[R] K2 & R K1 V1 V2 & L1 = K1.ⓑ{I}V1.
#R #I #L1 #K2 #V2 * #f #Hf #H
lapply (lexs_eq_repl_fwd … H (↑f) ?) -H /2 width=1 by eq_push_inv_isid/ #H
elim (lexs_inv_push2 … H) -H #Z1 #K1 #HK12 #HZ1 #H destruct
elim (ext2_inv_pair_dx … HZ1) -HZ1 #V1 #HV12 #H destruct
/3 width=5 by ex3_2_intro, ex2_intro/
qed-.

(* Advanced inversion lemmas ************************************************)

(* Basic_2A1: was: lpx_sn_inv_pair *)
lemma lex_inv_pair: ∀R,I1,I2,L1,L2,V1,V2.
                    L1.ⓑ{I1}V1 ⪤[R] L2.ⓑ{I2}V2 →
                    ∧∧ L1 ⪤[R] L2 & R L1 V1 V2 & I1 = I2.
#R #I1 #I2 #L1 #L2 #V1 #V2 #H elim (lex_inv_pair_sn … H) -H
#L0 #V0 #HL10 #HV10 #H destruct /2 width=1 by and3_intro/
qed-.

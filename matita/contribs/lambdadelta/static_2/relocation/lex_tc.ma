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

include "static_2/syntax/ext2_tc.ma".
include "static_2/relocation/sex_tc.ma".
include "static_2/relocation/lex.ma".

alias symbol "subseteq" = "relation inclusion".

(* GENERIC EXTENSION OF A CONTEXT-SENSITIVE REALTION FOR TERMS **************)

(* Inversion lemmas with transitive closure *********************************)

(* Basic_2A1: was: lpx_sn_LTC_TC_lpx_sn *)
lemma lex_inv_CTC (R): c_reflexive … R →
                       lex (CTC … R) ⊆ TC … (lex R).
#R #HR #L1 #L2 *
/5 width=11 by sex_inv_tc_dx, sex_co, ext2_inv_tc, ext2_refl, monotonic_TC, ex2_intro/
qed-.

lemma s_rs_transitive_lex_inv_isid (R): s_rs_transitive … R (λ_.lex R) →
                                        s_rs_transitive_isid cfull (cext2 R).
#R #HR #f #Hf #L2 #T1 #T2 #H #L1 #HL12
elim (ext2_tc … H) -H
[ /3 width=1 by ext2_inv_tc, ext2_unit/
| #I #V1 #V2 #HV12
  @ext2_inv_tc @ext2_pair
  @(HR … HV12) -HV12 /2 width=3 by ex2_intro/ (**) (* auto fails *)
]
qed-.

(* Properties with transitive closure ***************************************)

(* Basic_2A1: was: TC_lpx_sn_inv_lpx_sn_LTC *)
lemma lex_CTC (R): s_rs_transitive … R (λ_. lex R) →
                   TC … (lex R) ⊆ lex (CTC … R).
#R #HR #L1 #L2 #HL12
lapply (monotonic_TC … (sex cfull (cext2 R) 𝐈𝐝) … HL12) -HL12
[ #L1 #L2 * /3 width=3 by sex_eq_repl_fwd, eq_id_inv_isid/
| /5 width=9 by s_rs_transitive_lex_inv_isid, sex_tc_dx, sex_co, ext2_tc, ex2_intro/
]
qed-.

lemma lex_CTC_inj (R): s_rs_transitive … R (λ_. lex R) →
                       (lex R) ⊆ lex (CTC … R).
/3 width=1 by lex_CTC, inj/ qed-.

lemma lex_CTC_step_dx (R): c_reflexive … R → s_rs_transitive … R (λ_. lex R) →
                           ∀L1,L. lex (CTC … R) L1 L →
                           ∀L2. lex R L L2 → lex (CTC … R) L1 L2.
/4 width=3 by lex_CTC, lex_inv_CTC, step/ qed-.

lemma lex_CTC_step_sn (R): c_reflexive … R → s_rs_transitive … R (λ_. lex R) →
                           ∀L1,L. lex R L1 L →
                           ∀L2. lex (CTC … R) L L2 → lex (CTC … R) L1 L2.
/4 width=3 by lex_CTC, lex_inv_CTC, TC_strap/ qed-.

(* Eliminators with transitive closure **************************************)

lemma lex_CTC_ind_sn (R) (L2): c_reflexive … R → s_rs_transitive … R (λ_. lex R) →
                               ∀Q:predicate lenv. Q L2 →
                               (∀L1,L. L1 ⪤[R] L → L ⪤[CTC … R] L2 → Q L → Q L1) →
                               ∀L1. L1 ⪤[CTC … R] L2 → Q L1.
#R #L2 #H1R #H2R #Q #IH1 #IH2 #L1 #H
lapply (lex_inv_CTC … H1R … H) -H #H
@(TC_star_ind_dx ???????? H) -H
/3 width=4 by lex_CTC, lex_refl/
qed-.

lemma lex_CTC_ind_dx (R) (L1): c_reflexive … R → s_rs_transitive … R (λ_. lex R) →
                               ∀Q:predicate lenv. Q L1 →
                               (∀L,L2. L1 ⪤[CTC … R] L → L ⪤[R] L2 → Q L → Q L2) →
                               ∀L2. L1 ⪤[CTC … R] L2 → Q L2.
#R #L1 #H1R #H2R #Q #IH1 #IH2 #L2 #H
lapply (lex_inv_CTC … H1R … H) -H #H
@(TC_star_ind ???????? H) -H
/3 width=4 by lex_CTC, lex_refl/
qed-.

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

include "basic_2/syntax/ext2_tc.ma".
include "basic_2/relocation/lexs_tc.ma".
include "basic_2/relocation/lex.ma".

alias symbol "subseteq" = "relation inclusion".

(* GENERIC EXTENSION OF A CONTEXT-SENSITIVE REALTION FOR TERMS **************)

(* Inversion lemmas with transitive closure *********************************)

(* Basic_2A1: was: lpx_sn_LTC_TC_lpx_sn *)
lemma lex_inv_CTC: ∀R. c_reflexive … R →
                   lex (CTC … R) ⊆ TC … (lex R).
#R #HR #L1 #L2 *
/5 width=11 by lexs_inv_tc_dx, lexs_co, ext2_inv_tc, ext2_refl, monotonic_TC, ex2_intro/
qed-.

lemma s_rs_transitive_lex_inv_isid: ∀R. s_rs_transitive … R (λ_.lex R) →
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
lemma lex_CTC: ∀R. s_rs_transitive … R (λ_. lex R) →
               TC … (lex R) ⊆ lex (CTC … R).
#R #HR #L1 #L2 #HL12
lapply (monotonic_TC … (lexs cfull (cext2 R) 𝐈𝐝) … HL12) -HL12
[ #L1 #L2 * /3 width=3 by lexs_eq_repl_fwd, eq_id_inv_isid/
| /5 width=9 by s_rs_transitive_lex_inv_isid, lexs_tc_dx, lexs_co, ext2_tc, ex2_intro/
]
qed-.

lemma lex_CTC_step_dx: ∀R. c_reflexive … R → s_rs_transitive … R (λ_. lex R) →
                       ∀L1,L. lex (CTC … R) L1 L →
                       ∀L2. lex R L L2 → lex (CTC … R) L1 L2.
/4 width=3 by lex_CTC, lex_inv_CTC, step/ qed-.

lemma lex_CTC_step_sn: ∀R. c_reflexive … R → s_rs_transitive … R (λ_. lex R) →
                       ∀L1,L. lex R L1 L →
                       ∀L2. lex (CTC … R) L L2 → lex (CTC … R) L1 L2.
/4 width=3 by lex_CTC, lex_inv_CTC, TC_strap/ qed-.

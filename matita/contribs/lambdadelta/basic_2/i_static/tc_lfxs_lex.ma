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

include "basic_2/relocation/lex_tc.ma".
include "basic_2/static/lfeq_fqup.ma".
include "basic_2/static/lfeq_fsle.ma".
include "basic_2/i_static/tc_lfxs_fqup.ma".

(* ITERATED EXTENSION ON REFERRED ENTRIES OF A CONTEXT-SENSITIVE REALTION ***)

(* Properties with generic extension of a context sensitive relation ********)

lemma tc_lfxs_lex: ∀R. c_reflexive … R →
                   ∀L1,L2,T. L1 ⪤[LTC … R] L2 → L1 ⪤**[R, T] L2.
#R #HR #L1 #L2 #T *
/5 width=7 by tc_lfxs_tc, lexs_inv_tc_dx, lexs_co, ext2_inv_tc, ext2_refl/
qed.

lemma tc_lfxs_lex_lfeq: ∀R. c_reflexive … R →
                        ∀L1,L. L1 ⪤[LTC … R] L → ∀L2,T. L ≐[T] L2 →
                        L1 ⪤**[R, T] L2.
/3 width=3 by tc_lfxs_lex, tc_lfxs_step_dx, lfeq_fwd_lfxs/ qed.

(* Inversion lemmas with generic extension of a context sensitive relation **)

(* Note: s_rs_transitive_lex_inv_isid could be invoked in the last auto but makes it too slow *)
lemma tc_lfxs_inv_lex_lfeq: ∀R. c_reflexive … R →
                            lfxs_fsge_compatible R →
                            s_rs_transitive … R (λ_.lex R) →
                            lfeq_transitive R →
                            ∀L1,L2,T. L1 ⪤**[R, T] L2 →
                            ∃∃L. L1 ⪤[LTC … R] L & L ≐[T] L2.
#R #H1R #H2R #H3R #H4R #L1 #L2 #T #H
lapply (s_rs_transitive_lex_inv_isid … H3R) -H3R #H3R
@(tc_lfxs_ind_sn … H1R … H) -H -L2
[ /4 width=3 by lfeq_refl, lex_refl, inj, ex2_intro/
| #L0 #L2 #_ #HL02 * #L * #f0 #Hf0 #HL1 #HL0
  lapply (lfeq_lfxs_trans … HL0 … HL02) -L0 // * #f1 #Hf1 #HL2
  elim (lexs_sdj_split … ceq_ext … HL2 f0 ?) -HL2
  [ #L0 #HL0 #HL02 |*: /2 width=1 by ext2_refl, sdj_isid_dx/ ]
  lapply (lexs_sdj … HL0 f1 ?) /2 width=1 by sdj_isid_sn/ #H
  elim (frees_lexs_conf … Hf1 … H) // -H2R -H #f2 #Hf2 #Hf21
  lapply (sle_lexs_trans … HL02 … Hf21) -f1 // #HL02
  lapply (lexs_co ?? cfull (LTC … (cext2 R)) … HL1) -HL1 /2 width=1 by ext2_inv_tc/ #HL1
  /8 width=11 by lexs_inv_tc_dx, lexs_tc_dx, lexs_co, ext2_tc, ext2_refl, step, ex2_intro/ (**) (* full auto too slow *)
]
qed-.

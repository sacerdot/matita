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
include "basic_2/static/req_fqup.ma".
include "basic_2/static/req_fsle.ma".
include "basic_2/i_static/rexs_fqup.ma".

(* ITERATED EXTENSION ON REFERRED ENTRIES OF A CONTEXT-SENSITIVE REALTION ***)

(* Properties with generic extension of a context sensitive relation ********)

lemma rexs_lex: ∀R. c_reflexive … R →
                ∀L1,L2,T. L1 ⪤[CTC … R] L2 → L1 ⪤*[R, T] L2.
#R #HR #L1 #L2 #T *
/5 width=7 by rexs_tc, sex_inv_tc_dx, sex_co, ext2_inv_tc, ext2_refl/
qed.

lemma rexs_lex_req: ∀R. c_reflexive … R →
                    ∀L1,L. L1 ⪤[CTC … R] L → ∀L2,T. L ≡[T] L2 →
                    L1 ⪤*[R, T] L2.
/3 width=3 by rexs_lex, rexs_step_dx, req_fwd_rex/ qed.

(* Inversion lemmas with generic extension of a context sensitive relation **)

(* Note: s_rs_transitive_lex_inv_isid could be invoked in the last auto but makes it too slow *)
lemma rexs_inv_lex_req: ∀R. c_reflexive … R →
                        rex_fsge_compatible R →
                        s_rs_transitive … R (λ_.lex R) →
                        req_transitive R →
                        ∀L1,L2,T. L1 ⪤*[R, T] L2 →
                        ∃∃L. L1 ⪤[CTC … R] L & L ≡[T] L2.
#R #H1R #H2R #H3R #H4R #L1 #L2 #T #H
lapply (s_rs_transitive_lex_inv_isid … H3R) -H3R #H3R
@(rexs_ind_sn … H1R … H) -H -L2
[ /4 width=3 by req_refl, lex_refl, inj, ex2_intro/
| #L0 #L2 #_ #HL02 * #L * #f0 #Hf0 #HL1 #HL0
  lapply (req_rex_trans … HL0 … HL02) -L0 // * #f1 #Hf1 #HL2
  elim (sex_sdj_split … ceq_ext … HL2 f0 ?) -HL2
  [ #L0 #HL0 #HL02 |*: /2 width=1 by ext2_refl, sdj_isid_dx/ ]
  lapply (sex_sdj … HL0 f1 ?) /2 width=1 by sdj_isid_sn/ #H
  elim (frees_sex_conf … Hf1 … H) // -H2R -H #f2 #Hf2 #Hf21
  lapply (sle_sex_trans … HL02 … Hf21) -f1 // #HL02
  lapply (sex_co ?? cfull (CTC … (cext2 R)) … HL1) -HL1 /2 width=1 by ext2_inv_tc/ #HL1
  /8 width=11 by sex_inv_tc_dx, sex_tc_dx, sex_co, ext2_tc, ext2_refl, step, ex2_intro/ (**) (* full auto too slow *)
]
qed-.

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
include "basic_2/static/lfeq_fqup.ma".
include "basic_2/static/lfxs_lfxs.ma".
include "basic_2/i_static/tc_lfxs_fqup.ma".

(* ITERATED EXTENSION ON REFERRED ENTRIES OF A CONTEXT-SENSITIVE REALTION ***)

lemma tc_lfxs_inv_lex_lfeq: ∀R. c_reflexive … R →
                            (lexs_frees_confluent (cext2 R) cfull) →
                            (∀f. 𝐈⦃f⦄ → s_rs_transitive … (cext2 R) (λ_.lexs cfull (cext2 R) f)) →
                            ∀L1,L2,T. L1 ⪤**[R, T] L2 →
                            ∃∃L. L1 ⪤[LTC … R] L & L ≡[T] L2.
#R #H1R #H2R #H3R #L1 #L2 #T #H
@(tc_lfxs_ind_sn … H1R … H) -H -L2
[ /4 width=3 by lfeq_refl, lex_refl, inj, ex2_intro/
| #L0 #L2 #_ #HL02 * #L * #f0 #Hf0 #HL1 #HL0
  lapply (lfeq_lfxs_trans … HL0 … HL02) -L0 * #f1 #Hf1 #HL2
  elim (lexs_sdj_split … ceq_ext … HL2 f0 ?) -HL2
  [ #L0 #HL0 #HL02 |*: /2 width=1 by ext2_refl, sdj_isid_dx/ ]
  lapply (lexs_sdj … HL0 f1 ?) /2 width=1 by sdj_isid_sn/ #H
  elim (H2R … Hf1 … H) -H #f2 #Hf2 #Hf21
  lapply (sle_lexs_trans … HL02 … Hf21) -f1 // #HL02
  lapply (lexs_co ?? cfull (LTC … (cext2 R)) … HL1) -HL1 /2 width=1 by ext2_inv_tc/ #HL1  
  lapply (lexs_inv_tc_dx … HL1) -HL1 /2 width=1 by ext2_refl/ #HL1
  lapply (step ????? HL1 … HL0) -L #HL10
  lapply (lexs_tc_dx … H3R … HL10) -HL10 // #HL10
  lapply (lexs_co … cfull (cext2 (LTC … R)) … HL10) -HL10 /2 width=1 by ext2_tc/ #HL10
  /3 width=5 by ex2_intro/
]
qed-.

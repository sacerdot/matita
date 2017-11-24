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

(* GENERIC EXTENSION OF A CONTEXT-SENSITIVE REALTION FOR TERMS **************)

(* Inversion lemmas with transitive closure *********************************)

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

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

include "basic_2/relocation/lex.ma".
include "basic_2/static/lfxs_fqup.ma".

(* GENERIC EXTENSION ON REFERRED ENTRIES OF A CONTEXT-SENSITIVE REALTION ****)

(* Properties with generic extension of a context-sensitive relation ********)

lemma lfxs_lex: ∀R,L1,L2. L1 ⪤[R] L2 → ∀T. L1 ⪤*[R, T] L2.
#R #L1 #L2 * #f #Hf #HL12 #T
elim (frees_total L1 T) #g #Hg
/4 width=5 by lexs_sdj, sdj_isid_sn, ex2_intro/
qed.

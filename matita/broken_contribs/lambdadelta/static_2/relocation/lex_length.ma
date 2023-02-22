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

include "static_2/relocation/sex_length.ma".
include "static_2/relocation/lex.ma".

(* GENERIC EXTENSION OF A CONTEXT-SENSITIVE REALTION FOR TERMS **************)

(* Forward lemmas with length for local environments ************************)

(* Basic_2A1: was: lpx_sn_fwd_length *)
lemma lex_fwd_length: ∀R,L1,L2. L1 ⪤[R] L2 → |L1| = |L2|.
#R #L1 #L2 * /2 width=4 by sex_fwd_length/
qed-.

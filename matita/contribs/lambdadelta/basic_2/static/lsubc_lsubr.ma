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

include "basic_2/static/lsubr.ma".
include "basic_2/static/lsubc.ma".

(* LOCAL ENVIRONMENT REFINEMENT FOR GENERIC REDUCIBILITY ********************)

(* Forward lemmas with restricted refinement for local environments *********)

lemma lsubc_fwd_lsubr: ∀RP,G,L1,L2. G ⊢ L1 ⫃[RP] L2 → L1 ⫃ L2.
#RP #G #L1 #L2 #H elim H -L1 -L2 /2 width=1 by lsubr_pair, lsubr_beta/
qed-.

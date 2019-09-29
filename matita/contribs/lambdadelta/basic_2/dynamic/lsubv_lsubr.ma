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

include "static_2/static/lsubr.ma".
include "basic_2/dynamic/lsubv.ma".

(* LOCAL ENVIRONMENT REFINEMENT FOR NATIVE VALIDITY *************************)

(* Forward lemmas with restricted refinement for local environments *********)

(* Basic_2A1: uses: lsubsv_fwd_lsubr *)
lemma lsubv_fwd_lsubr (h) (a) (G): ∀L1,L2. G ⊢ L1 ⫃![h,a] L2 → L1 ⫃ L2.
#h #a #G #L1 #L2 #H elim H -L1 -L2 /2 width=1 by lsubr_bind, lsubr_beta/
qed-.

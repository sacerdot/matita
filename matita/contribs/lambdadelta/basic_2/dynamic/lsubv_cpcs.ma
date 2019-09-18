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

include "basic_2/rt_equivalence/cpcs_lsubr.ma".
include "basic_2/dynamic/lsubv_lsubr.ma".

(* LOCAL ENVIRONMENT REFINEMENT FOR NATIVE VALIDITY *************************)

(* Forward lemmas with context-sensitive r-equivalence for terms ************)

(* Basic_2A1: uses: lsubsv_cprs_trans *)
lemma lsubv_cpcs_trans (h) (a) (G): lsub_trans … (cpcs h G) (lsubv h a G).
/3 width=6 by lsubv_fwd_lsubr, lsubr_cpcs_trans/
qed-.

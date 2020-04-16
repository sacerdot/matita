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

include "basic_2/rt_transition/lpx.ma".
include "basic_2/rt_transition/cpm_cpx.ma".
include "basic_2/rt_transition/lpr.ma".

(* PARALLEL R-TRANSITION FOR FULL LOCAL ENVIRONMENTS ************************)

(* Forward lemmas with extended parallel rt-transition for ref local envs ***)

(* Basic_2A1: was: lpr_lpx *)
lemma lpr_fwd_lpx (h) (G):
      ∀L1,L2. ❪G,L1❫ ⊢ ➡[h,0] L2 → ❪G,L1❫ ⊢ ⬈ L2.
/3 width=3 by cpm_fwd_cpx, lex_co/ qed-.

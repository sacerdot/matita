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

include "basic_2/rt_transition/fpb_lpx.ma".
include "basic_2/rt_transition/lpr_lpx.ma".

(* PARALLEL R-TRANSITION FOR FULL LOCAL ENVIRONMENTS ************************)

(* Forward lemmas with rst-transition for closures **************************)

(* Basic_2A1: uses: lpr_fpbq *)
lemma lpr_fwd_fpb (h) (G) (T):
      ∀L1,L2. ❨G,L1❩ ⊢ ➡[h,0] L2 → ❨G,L1,T❩ ≽ ❨G,L2,T❩.
/3 width=2 by lpx_fpb, lpr_fwd_lpx/ qed-.

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

include "basic_2/static/lfxs_length.ma".
include "basic_2/rt_transition/lfpr.ma".

(* PARALLEL R-TRANSITION FOR LOCAL ENV.S ON REFERRED ENTRIES ****************)

(* Forward lemmas with length for local environments ************************)

lemma lfpr_fwd_length: ∀h,G,L1,L2,T. ⦃G, L1⦄ ⊢ ➡[h, T] L2 → |L1| = |L2|.
/2 width=3 by lfxs_fwd_length/ qed-.

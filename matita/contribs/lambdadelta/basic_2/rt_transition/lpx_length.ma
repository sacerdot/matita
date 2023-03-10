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

include "static_2/relocation/lex_length.ma".
include "basic_2/rt_transition/lpx.ma".

(* EXTENDED PARALLEL RT-TRANSITION FOR FULL LOCAL ENVIRONMENTS **************)

(* Forward lemmas with length for local environments ************************)

lemma lpx_fwd_length (G):
      ∀L1,L2. ❨G,L1❩ ⊢ ⬈ L2 → |L1| = |L2|.
/2 width=2 by lex_fwd_length/ qed-.

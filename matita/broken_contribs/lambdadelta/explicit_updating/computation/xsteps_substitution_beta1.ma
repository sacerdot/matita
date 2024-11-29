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

include "explicit_updating/reduction/xbeta1.ma".
include "explicit_updating/computation/xsteps_substitution.ma".

(* X-COMPUTATION FOR SUBSTITUTION *******************************************)

(* Constructions with xbeta1 ************************************************)

lemma xsteps_subst_push_unwind (b) (f):
      (⫯𝐬❨f❩) ➡*[𝛃b] 𝐬❨⫯f❩.
#b #f * [| #p ]
[ /2 width=1 by xsteps_term_refl/
| <subst_push_succ <subst_unwind_dapp <subst_unwind_dapp
  <term_next_unfold <fbr_dapp_push_dx_succ
  @xsteps_term_step @xstep_term_step
  @xbeta1_unwind [3: // | skip | skip ] <unwind_lref //
]
qed.

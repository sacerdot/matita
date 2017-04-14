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

include "basic_2/static/lfxs_fqup.ma".
include "basic_2/rt_transition/lfpr.ma".

(* PARALLEL R-TRANSITION FOR LOCAL ENV.S ON REFERRED ENTRIES ****************)

(* Advanced properties ******************************************************)

(* Note: lemma 250 *)
(* Basic_2A1: uses: lpr_refl *)
lemma lfpr_refl: ∀h,G,T. reflexive … (lfpr h G T).
/2 width=1 by lfxs_refl/ qed.

(* Basic_2A1: uses: lpr_pair *)
lemma lfpr_pair: ∀h,G,L,V1,V2. ⦃G, L⦄ ⊢ V1 ➡[h] V2 →
                 ∀I,T. ⦃G, L.ⓑ{I}V1⦄ ⊢ ➡[h, T] L.ⓑ{I}V2.
/2 width=1 by lfxs_pair/ qed.

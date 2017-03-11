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
include "basic_2/rt_transition/lfpx.ma".

(* UNCOUNTED PARALLEL RT-TRANSITION FOR LOCAL ENV.S ON REFERRED ENTRIES *****)

(* Advanced properties ******************************************************)

lemma lfpx_refl: ∀h,G,T. reflexive … (lfpx h G T).
/2 width=1 by lfxs_refl/ qed.

lemma lfpx_pair: ∀h,G,L,V1,V2. ⦃G, L⦄ ⊢ V1 ⬈[h] V2 →
                 ∀I,T. ⦃G, L.ⓑ{I}V1⦄ ⊢ ⬈[h, T] L.ⓑ{I}V2.
/2 width=1 by lfxs_pair/ qed.

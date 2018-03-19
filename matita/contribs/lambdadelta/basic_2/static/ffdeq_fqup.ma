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

include "basic_2/static/lfdeq_fqup.ma".
include "basic_2/static/ffdeq.ma".

(* DEGREE-BASED EQUIVALENCE FOR CLOSURES ON REFERRED ENTRIES ****************)

(* Properties with degree-based equivalence for terms ***********************)

lemma tdeq_ffdeq: ∀h,o,T1,T2. T1 ≛[h, o] T2 →
                  ∀G,L. ⦃G, L, T1⦄ ≛[h, o] ⦃G, L, T2⦄.
/2 width=1 by ffdeq_intro_sn/ qed.

(* Advanced properties ******************************************************)

lemma ffdeq_refl: ∀h,o. tri_reflexive … (ffdeq h o).
/2 width=1 by ffdeq_intro_sn/ qed.

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

include "static_2/static/rdeq_fqup.ma".
include "static_2/static/fdeq.ma".

(* DEGREE-BASED EQUIVALENCE FOR CLOSURES ON REFERRED ENTRIES ****************)

(* Properties with degree-based equivalence for terms ***********************)

lemma tdeq_fdeq: ∀h,o,T1,T2. T1 ≛[h, o] T2 →
                 ∀G,L. ⦃G, L, T1⦄ ≛[h, o] ⦃G, L, T2⦄.
/2 width=1 by fdeq_intro_sn/ qed.

(* Advanced properties ******************************************************)

lemma fdeq_refl: ∀h,o. tri_reflexive … (fdeq h o).
/2 width=1 by fdeq_intro_sn/ qed.

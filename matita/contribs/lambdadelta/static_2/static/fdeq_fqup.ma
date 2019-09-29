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

(* SORT-IRRELEVANT EQUIVALENCE FOR CLOSURES ON REFERRED ENTRIES *************)

(* Properties with sort-irrelevant equivalence for terms ********************)

lemma tdeq_fdeq: ∀T1,T2. T1 ≛ T2 →
                 ∀G,L. ⦃G,L,T1⦄ ≛ ⦃G,L,T2⦄.
/2 width=1 by fdeq_intro_sn/ qed.

(* Advanced properties ******************************************************)

lemma fdeq_refl: tri_reflexive … fdeq.
/2 width=1 by fdeq_intro_sn/ qed.

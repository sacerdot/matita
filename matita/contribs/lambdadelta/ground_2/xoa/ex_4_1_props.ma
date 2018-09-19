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

include "ground_2/xoa/xoa.ma".

(* Properties with multiple existental quantifier (5, 1) ********************)

lemma ex4_commute (A0) (P0,P1,P2,P3:A0→Prop):
                  (∃∃x0. P0 x0 & P1 x0 & P2 x0 & P3 x0) → ∃∃x0. P2 x0 & P3 x0 & P0 x0 & P1 x0.
#A0 #P0 #P1 #P2 #P3 * /2 width=5 by ex4_intro/
qed-.

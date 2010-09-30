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



include "NLE/defs.ma".

theorem nle_nplus: ∀p, q, r. p ⊕ q ≍ r → q ≤ r.
 intros; elim H; clear H q r; autobatch.
qed.

axiom nle_nplus_comp: ∀x1,x2,x3. x1 ⊕ x2 ≍ x3 → ∀y1,y2,y3. y1 ⊕ y2 ≍ y3 →
                      x1 ≤ y1 → x2 ≤ y2 → x3 ≤ y3.

axiom nle_nplus_comp_lt_2: ∀x1,x2,x3. x1 ⊕ x2 ≍ x3 → ∀y1,y2,y3. y1 ⊕ y2 ≍ y3 →
                           x1 ≤ y1 → x2 < y2 → x3 < y3.

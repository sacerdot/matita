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

include "basic_2/multiple/mr2.ma".

(* MULTIPLE RELOCATION WITH PAIRS *******************************************)

let rec pluss (des:list2 nat nat) (i:nat) on des ≝ match des with
[ nil2          ⇒ ⟠
| cons2 d e des ⇒ {d + i, e} @ pluss des i
].

interpretation "plus (multiple relocation with pairs)"
   'plus x y = (pluss x y).

(* Basic inversion lemmas ***************************************************)

lemma pluss_inv_nil2: ∀i,des. des + i = ⟠ → des = ⟠.
#i * // normalize
#d #e #des #H destruct
qed.

lemma pluss_inv_cons2: ∀i,d,e,des2,des. des + i = {d, e} @ des2 →
                       ∃∃des1. des1 + i = des2 & des = {d - i, e} @ des1.
#i #d #e #des2 * normalize
[ #H destruct
| #d1 #e1 #des1 #H destruct /2 width=3/
]
qed-.

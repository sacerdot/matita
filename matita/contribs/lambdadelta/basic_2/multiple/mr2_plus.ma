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
[ nil2          ⇒ ◊
| cons2 l m des ⇒ {l + i, m} @ pluss des i
].

interpretation "plus (multiple relocation with pairs)"
   'plus x y = (pluss x y).

(* Basic inversion lemmas ***************************************************)

lemma pluss_inv_nil2: ∀i,des. des + i = ◊ → des = ◊.
#i * // normalize
#l #m #des #H destruct
qed.

lemma pluss_inv_cons2: ∀i,l,m,des2,des. des + i = {l, m} @ des2 →
                       ∃∃des1. des1 + i = des2 & des = {l - i, m} @ des1.
#i #l #m #des2 * normalize
[ #H destruct
| #l1 #m1 #des1 #H destruct /2 width=3/
]
qed-.

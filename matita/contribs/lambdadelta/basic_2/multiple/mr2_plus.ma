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

let rec pluss (cs:list2 nat nat) (i:nat) on cs ≝ match cs with
[ nil2          ⇒ ◊
| cons2 l m cs ⇒ {l + i, m} @ pluss cs i
].

interpretation "plus (multiple relocation with pairs)"
   'plus x y = (pluss x y).

(* Basic inversion lemmas ***************************************************)

lemma pluss_inv_nil2: ∀i,cs. cs + i = ◊ → cs = ◊.
#i * // normalize
#l #m #cs #H destruct
qed.

lemma pluss_inv_cons2: ∀i,l,m,cs2,cs. cs + i = {l, m} @ cs2 →
                       ∃∃cs1. cs1 + i = cs2 & cs = {l - i, m} @ cs1.
#i #l #m #cs2 * normalize
[ #H destruct
| #l1 #m1 #cs1 #H destruct /2 width=3 by ex2_intro/
]
qed-.

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

include "Basic_2/grammar/term_vector.ma".

(* GENERIC RELOCATION WITH PAIRS ********************************************)

let rec pluss (des:list2 nat nat) (i:nat) on des ≝ match des with
[ nil2          ⇒ ⟠
| cons2 d e des ⇒ {d + i, e} :: pluss des i
].

interpretation "plus (generic relocation with pairs)"
   'plus x y = (pluss x y).

inductive at: list2 nat nat → relation nat ≝
| at_nil: ∀i. at ⟠ i i
| at_lt : ∀des,d,e,i1,i2. i1 < d →
          at des i1 i2 → at ({d, e} :: des) i1 i2
| at_ge : ∀des,d,e,i1,i2. d ≤ i1 →
          at des (i1 + e) i2 → at ({d, e} :: des) i1 i2
.

interpretation "application (generic relocation with pairs)"
   'RAt i1 des i2 = (at des i1 i2).

inductive minuss: nat → relation (list2 nat nat) ≝
| minuss_nil: ∀i. minuss i ⟠ ⟠ 
| minuss_lt : ∀des1,des2,d,e,i. i < d → minuss i des1 des2 →
              minuss i ({d, e} :: des1) ({d - i, e} :: des2)
| minuss_ge : ∀des1,des2,d,e,i. d ≤ i → minuss (e + i) des1 des2 →
              minuss i ({d, e} :: des1) des2
.

interpretation "minus (generic relocation with pairs)"
   'RMinus des1 i des2 = (minuss i des1 des2).

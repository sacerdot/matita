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

include "ground/notation/functions/one_0.ma".
include "ground/notation/functions/uparrow_1.ma".
include "ground/lib/relations.ma".

(* POSITIVE INTEGERS ********************************************************)

inductive pnat: Type[0] ≝
| punit: pnat
| psucc: pnat → pnat
.

interpretation
  "unit (positive integers)"
  'One = (punit).

interpretation
  "successor (positive integers)"
  'UpArrow p = (psucc p).

(* Basic inversions *********************************************************)

(* Note: destruct *)
lemma eq_inv_psucc_bi: injective … psucc.
#p #q #H destruct //
qed.

(* Basic constructions ******************************************************)

lemma eq_pnat_dec (p1,p2:pnat): Decidable (p1 = p2).
#p1 elim p1 -p1 [| #p1 #IH ] * [2,4: #p2 ]
[1,4: @or_intror #H destruct
| elim (IH p2) -IH #H destruct
  /4 width=1 by eq_inv_psucc_bi, or_intror, or_introl/
| /2 width=1 by or_introl/
]
qed-.

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

include "ground_2/notation/functions/norm_1.ma".
include "ground_2/lib/bool.ma".
include "ground_2/lib/list.ma".

(* RELOCATION TRACE *********************************************************)

definition trace: Type[0] ≝ list bool.

let rec colength (cs:trace) on cs ≝ match cs with
[ nil       ⇒ 0
| cons b tl ⇒ match b with [ true ⇒  ⫯(colength tl) | false ⇒ colength tl ] 
].

interpretation "colength (trace)"
   'Norm cs = (colength cs).

(* basic properties *********************************************************)

lemma colength_empty: ∥◊∥ = 0.
// qed.

lemma colength_true: ∀cs. ∥Ⓣ@cs∥ = ⫯∥cs∥.
// qed.

lemma colength_false: ∀cs. ∥Ⓕ@cs∥ = ∥cs∥.
// qed.

lemma colength_cons: ∀cs1,cs2. ∥cs1∥ = ∥cs2∥ →
                     ∀b. ∥b@cs1∥ = ∥b@cs2∥.
#cs1 #cs2 #H * /2 width=1 by/
qed.

lemma colength_le: ∀cs. ∥cs∥ ≤ |cs|.
#cs elim cs -cs //
* /2 width=1 by le_S_S, le_S/
qed.

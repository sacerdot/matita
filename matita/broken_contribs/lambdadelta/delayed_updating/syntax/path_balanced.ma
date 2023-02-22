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

include "delayed_updating/syntax/path.ma".
include "delayed_updating/notation/functions/class_b_0.ma".

(* BALANCE CONDITION FOR PATH ***********************************************)

(* Note: this condition applies to a structural path *)
inductive pbc: predicate path ≝
| pbc_empty: pbc (𝐞)
| pbc_redex: ∀b. pbc b → pbc (𝗔◗b◖𝗟)
| pbc_after: ∀b1,b2. pbc b1 → pbc b2 → pbc (b1●b2)
.

interpretation
  "balance condition (path)"
  'ClassB = (pbc).

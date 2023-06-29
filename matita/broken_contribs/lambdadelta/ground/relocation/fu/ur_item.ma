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

include "ground/arith/nat.ma".
include "ground/notation/relations/category_ui_0.ma".
include "ground/notation/functions/item_p_0.ma".
include "ground/notation/functions/item_j_1.ma".

(* RELOCATION ITEMS FOR UNWIND **********************************************)

inductive ur_item: Type[0] ≝
| ur_p: ur_item
| ur_j: ℕ → ur_item
.

interpretation
  "relocation items for unwind"
  'CategoryUI = (ur_item).

interpretation
  "push (relocation items for unwind)"
  'ItemP = (ur_p).

interpretation
  "iterated join (relocation items for unwind)"
  'ItemJ n = (ur_j n).

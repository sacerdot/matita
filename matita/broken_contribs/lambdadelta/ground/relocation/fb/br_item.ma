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

include "ground/lib/bool.ma".
include "ground/notation/relations/category_bi_0.ma".
include "ground/notation/functions/item_p_0.ma".
include "ground/notation/functions/item_n_0.ma".

(* RELOCATION ITEMS WITH BOLEANS ********************************************)

definition br_item: Type[0] ≝ bool.

interpretation
  "relocation items with booleans"
  'CategoryBI = (br_item).

interpretation
  "push (relocation items with booleans)"
  'ItemP = (false).

interpretation
  "next (relocation items with booleans)"
  'ItemN = (true).

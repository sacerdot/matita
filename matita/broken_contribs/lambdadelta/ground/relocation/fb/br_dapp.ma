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

include "ground/relocation/fb/br_item.ma".
include "ground/arith/pnat_split.ma".
include "ground/notation/functions/upspoon_1.ma".
include "ground/notation/functions/atsharp_2.ma".

(* DEPTH APPLICATION FOR RELOCATION ITEMS WITH BOOLOEANS ********************)

definition br_next (f): ℕ⁺ → ℕ⁺ ≝
           λp.↑(f p).

interpretation
  "next (relocation items with booleans)"
  'UpArrow f = (br_next f).

definition br_push (f): ℕ⁺ → ℕ⁺ ≝
  psplit … (𝟏) (↑f).

interpretation
  "push (relocation items with booleans)"
  'UpSpoon f = (br_push f).

definition br_dapp (b) (f): ℕ⁺ → ℕ⁺ ≝
if b then ↑f else (⫯f).

interpretation
  "depth application (relocation items with booleans)"
  'AtSharp b f = (br_dapp b f).

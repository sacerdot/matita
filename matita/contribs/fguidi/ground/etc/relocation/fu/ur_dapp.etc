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

include "ground/relocation/fu/ur_item.ma".
include "ground/arith/nat_rplus.ma".
include "ground/notation/functions/upspoon_1.ma".
include "ground/notation/functions/rightuparrowstar_2.ma".
include "ground/notation/functions/atsharp_2.ma".

(* DEPTH APPLICATION FOR RELOCATION ITEMS FOR UNWIND ************************)

definition ur_push (f) (p): ℕ⁺ ≝
match p with
[ punit   ⇒ 𝟏
| psucc q ⇒ ↑(f q)
].

interpretation
  "push (relocation items for unwind)"
  'UpSpoon f = (ur_push f).

definition ur_join (f) (n) (p): ℕ⁺ ≝
           f (p+n).

interpretation
  "join (relocation items for unwind)"
  'RightUpArrowStar n f = (ur_join f n).

definition ur_dapp (i) (f): ℕ⁺ → ℕ⁺ ≝
match i with
[ ur_p   ⇒ ⫯f
| ur_j n ⇒ ⮤*[n]f
].

interpretation
  "depth application (relocation items for unwind)"
  'AtSharp i f = (ur_dapp i f).

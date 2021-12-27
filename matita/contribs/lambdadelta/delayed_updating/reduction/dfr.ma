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

include "ground/xoa/ex_3_1.ma".
include "delayed_updating/syntax/path_structure.ma".
include "delayed_updating/syntax/path_balanced.ma".
include "delayed_updating/substitution/fsubst.ma".
include "delayed_updating/notation/relations/black_rightarrow_4.ma".

(* DELAYED FOCALIZED REDUCTION **********************************************)

inductive dfr (p) (q) (t): predicate preterm ≝
| dfr_beta (b) (n):
  let r ≝ p●𝗔◗b●𝗟◗q◖𝗱❨n❩ in
  r ϵ t → ⊓⊗b → dfr p q t (t[⋔r←t⋔(p◖𝗦)])
.

interpretation
  "delayed focalized reduction (preterm)"
  'BlackRightArrow t1 p q t2 = (dfr p q t1 t2).

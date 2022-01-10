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

include "delayed_updating/syntax/path_depth.ma".
include "delayed_updating/syntax/path_structure.ma".
include "delayed_updating/syntax/path_balanced.ma".
include "delayed_updating/substitution/fsubst.ma".
include "delayed_updating/notation/relations/black_rightarrow_df_4.ma".

(* DELAYED FOCUSED REDUCTION ************************************************)

inductive dfr (p) (q) (t): predicate preterm ≝
| dfr_beta (b):
  let r ≝ p●𝗔◗b●𝗟◗q◖𝗱(↑❘q❘) in
  r ϵ t → ⊓(⊗b) → dfr p q t (t[⋔r←t⋔(p◖𝗦)])
.

interpretation
  "focused balanced reduction with delayed updating (preterm)"
  'BlackRightArrowDF t1 p q t2 = (dfr p q t1 t2).

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

include "delayed_updating/syntax/path_structure.ma".
include "delayed_updating/syntax/path_balanced.ma".
include "delayed_updating/substitution/fsubst.ma".
include "delayed_updating/substitution/lift_preterm.ma".
include "delayed_updating/notation/relations/black_rightarrow_f_4.ma".

(* IMMEDIATE FOCUSED REDUCTION ************************************************)

inductive ifr (p) (q) (t): predicate preterm ≝
| ifr_beta (b) (n):
  let r ≝ p●𝗔◗b●𝗟◗q in
  r◖𝗱❨n❩ ϵ t → ⊓⊗b → ifr p q t (t[⋔r←↑[𝐮❨n❩]t⋔(p◖𝗦)])
.

interpretation
  "focused balanced reduction with immediate updating (preterm)"
  'BlackRightArrowF t1 p q t2 = (ifr p q t1 t2).

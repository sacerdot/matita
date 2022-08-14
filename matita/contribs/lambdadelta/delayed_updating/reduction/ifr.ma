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

include "delayed_updating/substitution/fsubst.ma".
include "delayed_updating/substitution/lift_prototerm.ma".
include "delayed_updating/syntax/prototerm_eq.ma".
include "delayed_updating/syntax/path_head.ma".
include "delayed_updating/notation/relations/black_rightarrow_if_3.ma".
include "ground/relocation/tr_uni.ma".
include "ground/xoa/ex_4_3.ma".

(* IMMEDIATE FOCUSED REDUCTION ************************************************)

(**) (* explicit ninj because we cannot declare the expectd type of k *)
definition ifr (r): relation2 prototerm prototerm ≝
           λt1,t2.
           ∃∃p,q,k. p●𝗔◗𝗟◗q = r &
           (𝗟◗q) = ↳[ninj k](𝗟◗q) & r◖𝗱k ϵ t1 &
           t1[⋔r←↑[𝐮❨ninj k❩](t1⋔(p◖𝗦))] ⇔ t2
.

interpretation
  "focused reduction with immediate updating (prototerm)"
  'BlackRightArrowIF t1 r t2 = (ifr r t1 t2).

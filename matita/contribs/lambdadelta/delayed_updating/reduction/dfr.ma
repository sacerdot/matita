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
include "delayed_updating/syntax/prototerm_constructors.ma".
include "delayed_updating/syntax/prototerm_eq.ma".
include "delayed_updating/syntax/path_head.ma".
include "delayed_updating/syntax/path_depth.ma".
include "delayed_updating/notation/relations/black_rightarrow_df_3.ma".
include "ground/xoa/ex_4_3.ma".

(* DELAYED FOCUSED REDUCTION ************************************************)

(**) (* explicit ninj because we cannot declare the expectd type of k *)
definition dfr (r): relation2 prototerm prototerm ≝
           λt1,t2.
           ∃∃p,q,k. p●𝗔◗𝗟◗q = r &
           (𝗟◗q) = ↳[ninj k](𝗟◗q) & r◖𝗱k ϵ t1 &
           t1[⋔r←𝛕k.(t1⋔(p◖𝗦))] ⇔ t2
.

interpretation
  "focused reduction with delayed updating (prototerm)"
  'BlackRightArrowDF t1 r t2 = (dfr r t1 t2).

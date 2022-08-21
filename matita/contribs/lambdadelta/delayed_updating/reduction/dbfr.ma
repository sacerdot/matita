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
include "delayed_updating/syntax/path_balanced.ma".
include "delayed_updating/syntax/path_structure.ma".
include "delayed_updating/notation/relations/black_rightarrow_dbf_3.ma".
include "ground/arith/nat_rplus.ma".
include "ground/xoa/ex_6_5.ma".

(* DELAYED BALANCED FOCUSED REDUCTION ***************************************)

(**) (* explicit ninj because we cannot declare the expectd type of k *)
definition dbfr (r): relation2 prototerm prototerm ≝
           λt1,t2.
           ∃∃p,b,q,h,k. p●𝗔◗b●𝗟◗q = r &
           ⊗b ϵ 𝐁 & b = ↳[h]b &
           (𝗟◗q) = ↳[ninj k](𝗟◗q) & r◖𝗱k ϵ t1 &
           t1[⋔r←𝛕(k+h).(t1⋔(p◖𝗦))] ⇔ t2
.

interpretation
  "balanced focused reduction with delayed updating (prototerm)"
  'BlackRightArrowDBF t1 r t2 = (dbfr r t1 t2).

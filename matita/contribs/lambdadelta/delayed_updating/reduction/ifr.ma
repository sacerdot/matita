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
include "delayed_updating/notation/relations/black_rightarrow_if_4.ma".
include "ground/relocation/tr_uni.ma".

(* IMMEDIATE FOCUSED REDUCTION ************************************************)

definition ifr (p) (q): relation2 prototerm prototerm ≝
           λt1,t2. ∃k:pnat.
           let r ≝ p●𝗔◗𝗟◗q in
           ∧∧ 𝗟◗q = ↳[k](𝗟◗q) & r◖𝗱k ϵ t1 &
              t1[⋔r←↑[𝐮❨k❩](t1⋔(p◖𝗦))] ⇔ t2
.

interpretation
  "focused reduction with immediate updating (prototerm)"
  'BlackRightArrowIF t1 p q t2 = (ifr p q t1 t2).

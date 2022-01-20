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
include "delayed_updating/substitution/lift_prototerm.ma".
include "delayed_updating/notation/relations/black_rightarrow_f_4.ma".

(* IMMEDIATE FOCUSED REDUCTION ************************************************)

definition ifr (p) (q): relation2 prototerm prototerm ≝
           λt1,t2. ∃b.
           let r ≝ p●𝗔◗b●𝗟◗q in
           ∧∧ ⊓(⊗b) & r◖𝗱(↑❘q❘) ϵ t1 &
              t2 ⇔ t1[⋔r←↑[𝐮❨↑❘q❘❩]t1⋔(p◖𝗦)]
.

interpretation
  "focused balanced reduction with immediate updating (prototerm)"
  'BlackRightArrowF t1 p q t2 = (ifr p q t1 t2).

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
include "delayed_updating/syntax/path_reverse.ma".
include "delayed_updating/notation/relations/black_rightarrow_df_4.ma".

(* DELAYED FOCUSED REDUCTION ************************************************)

definition dfr (p) (q): relation2 prototerm prototerm ≝
           λt1,t2. ∃n:pnat.
           let r ≝ p●𝗔◗𝗟◗q in
           ∧∧ (𝗟◗q)ᴿ = ↳[n](𝗟◗q)ᴿ & r◖𝗱n ϵ t1 &
              t1[⋔r←𝛕n.(t1⋔(p◖𝗦))] ⇔ t2
.

interpretation
  "focused reduction with delayed updating (prototerm)"
  'BlackRightArrowDF t1 p q t2 = (dfr p q t1 t2).

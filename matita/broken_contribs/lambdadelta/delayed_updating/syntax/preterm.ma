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

include "delayed_updating/syntax/prototerm.ma".
include "delayed_updating/notation/functions/class_t_0.ma".

(* PRETERM ******************************************************************)

record preterm_axs (t): Prop ≝
  { term_complete_ax (p1) (p2):
(* Note: we cannot extend complete paths *)
      p1 ϵ t → p2 ϵ t → p1 ϵ ↑p2 → p1 = p2
  ; term_root_ax (p) (l1) (k2):
(* Note: root paths do not diverge on varible references *)
      p◖l1 ϵ ▵t → p◖𝗱k2 ϵ ▵t → l1 = 𝗱k2
(* Note: applications have arguments *)
  ; term_full_A_ax (p):
      p◖𝗔 ϵ ▵t → p◖𝗦 ϵ ▵t
  }.

interpretation
  "preterm (prototerm)"
  'ClassT = (preterm_axs).

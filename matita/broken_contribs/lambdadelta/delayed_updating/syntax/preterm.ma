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
  { term_complete_ax:
(* Note: we cannot extend complete paths *)
      ∀p1,p2. p1 ϵ t → p2 ϵ t → p1 ϵ ↑p2 → p1 = p2
  ; term_root_ax:
(* Note: root paths do not diverge on varible references *)
      ∀p,l1,k2. p◖l1 ϵ ▵t → p◖𝗱k2 ϵ ▵t → l1 = 𝗱k2
  }.

interpretation
  "preterm (prototerm)"
  'ClassT = (preterm_axs).

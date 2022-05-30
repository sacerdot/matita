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

include "delayed_updating/substitution/lift_prototerm.ma".
include "delayed_updating/substitution/lift_path_proper.ma".
include "delayed_updating/syntax/prototerm_proper.ma".

(* LIFT FOR PROTOTERM *******************************************************)

(* Constructions with proper condition for path *****************************)

lemma lift_term_proper (f) (t):
      t ϵ 𝐏 → ↑[f]t ϵ 𝐏.
#f #t #Ht #p * #q #Hq #H0 destruct
@lift_path_proper @Ht -Ht // (**) (* auto fails *)
qed.

(* Inversions with proper condition for path ********************************)

lemma lift_term_inv_proper (f) (t):
      ↑[f]t ϵ 𝐏 → t ϵ 𝐏.
#f #t #Ht #p #Hp
@(lift_path_inv_proper f)
@Ht -Ht @in_comp_lift_bi // (**) (* auto fails *)
qed-.

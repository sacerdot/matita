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

include "delayed_updating/substitution/lift_prototerm_eq.ma".
include "delayed_updating/reduction/prototerm_focus.ma".

(* BALANCED REDUCTION FOCUS *************************************************)

(* Constructions with lift **************************************************)

lemma brf_lift (f) (t) (p) (b) (q):
      (🠡[f]t) ∩ 𝐅❨🠡[f]p, 🠡[🠢[p◖𝗔]f]b, 🠡[🠢[(p◖𝗔)●b◖𝗟]f]q❩ ⇔ (🠡[f]t) ∩ 🠡[f]𝐅❨p,b,q❩.
#t #f #p #b #q
<brf_unfold <brf_unfold //
qed.

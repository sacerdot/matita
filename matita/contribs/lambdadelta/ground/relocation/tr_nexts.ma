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

include "ground/arith/nat_pred_succ.ma".
include "ground/relocation/pr_nexts.ma".
include "ground/relocation/tr_map.ma".

(* TOTAL RELOCATION MAPS ****************************************************)

(* Advanced constructions with pr_nexts *************************************)

lemma tr_inj_unfold (f):
      ∀p. ↑*[↓p]⫯𝐭❨f❩ = 𝐭❨p⨮f❩.
#f #p elim p -p //
qed.

lemma tr_inj_fold (f):
      ∀p. 𝐭❨p⨮f❩ = ↑*[↓p]⫯𝐭❨f❩.
// qed.

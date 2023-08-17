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

include "delayed_updating/unwind_k/unwind2_rmap.ma".
include "ground/relocation/fb/fbr_uni_ctls.ma".

(* TAILED UNWIND FOR RELOCATION MAP *****************************************)

(* Constructions with map_ctls **********************************************)

lemma ctls_unwind2_rmap_d_dx (f) (p) (n) (k):
      (⫰*[(⁤n)+k]▶[p]f) = ⫰*[⁤n]▶[p◖𝗱(k)]f.
// qed.

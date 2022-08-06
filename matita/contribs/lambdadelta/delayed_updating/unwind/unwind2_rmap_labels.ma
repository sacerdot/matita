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

include "delayed_updating/unwind/unwind2_rmap.ma".
include "delayed_updating/syntax/path_labels.ma".
include "ground/relocation/tr_pushs.ma".

(* TAILED UNWIND FOR RELOCATION MAP *****************************************)

(* Constructions with labels ************************************************)

lemma unwind2_rmap_labels_L (f) (n):
      (⫯*[n]f) = ▶[f](𝗟∗∗n).
#f #n @(nat_ind_succ … n) -n //
#n #IH
<labels_succ <unwind2_rmap_L_dx //
qed.

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
include "delayed_updating/syntax/path_labels.ma".

(* DEPTH FOR PATH ***********************************************************)

(* Constructions with labels ************************************************)

lemma depth_labels_L (n):
      n = ♭(𝗟∗∗n).
#n @(nat_ind_succ … n) -n //
#n #IH <labels_succ <depth_L_dx //
qed.

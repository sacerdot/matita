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

include "delayed_updating/unwind/unwind2_prototerm.ma".
include "delayed_updating/unwind/unwind2_path_append.ma".
include "ground/subsets/subset_ol.ma".

(* TAILED UNWIND FOR PROTOTERM **********************************************)

(* Destructions with pic ****************************************************)

lemma unwind2_term_des_pic (f) (t):
      ▼[f]t ≬ 𝐈 → t ≬ 𝐈.
#f #t * #p * #q #Hq #H0 #Hp destruct
@(subset_ol_i … Hq) -Hq (**) (* auto does not work *)
@(unwind2_path_des_pic … Hp)
qed-.

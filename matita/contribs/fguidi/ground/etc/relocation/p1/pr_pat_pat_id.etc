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

include "ground/relocation/p1/pr_pat_id.ma".
include "ground/relocation/p1/pr_pat_pat.ma".

(* POSITIVE APPLICATION FOR PARTIAL RELOCATION MAPS *************************)

(* Advanced destructions with pr_id *****************************************)

(*** at_id_fwd *)
lemma pr_pat_id_des (i1) (i2):
      ＠⧣❨i1,𝐢❩ ≘ i2 → i1 = i2.
/2 width=4 by pr_pat_mono/ qed-.

(* Main constructions with pr_id ********************************************)

(*** at_div_id_dx *)
theorem pr_pat_div_id_dx (f):
        H_pr_pat_div f (𝐢 ) (𝐢) f.
#f #jf #j0 #j #Hf #H0
lapply (pr_pat_id_des … H0) -H0 #H destruct
/2 width=3 by ex2_intro/
qed-.

(*** at_div_id_sn *)
theorem pr_pat_div_id_sn (f):
        H_pr_pat_div (𝐢) f f (𝐢).
/3 width=6 by pr_pat_div_id_dx, pr_pat_div_comm/ qed-.

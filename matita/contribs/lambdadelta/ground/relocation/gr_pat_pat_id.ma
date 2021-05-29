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

include "ground/relocation/gr_pat_id.ma".
include "ground/relocation/gr_pat_pat.ma".

(* POSITIVE APPLICATION FOR GENERIC RELOCATION MAPS *************************)

(* Advanced destructions with gr_id *****************************************)

(*** at_id_fwd *)
lemma gr_pat_id_des (i1) (i2):
      @❪i1,𝐢❫ ≘ i2 → i1 = i2.
/2 width=4 by gr_pat_mono/ qed-.

(* Main constructions with gr_id ********************************************)

(*** at_div_id_dx *)
theorem gr_pat_div_id_dx (f):
        H_gr_pat_div f 𝐢 𝐢 f.
#f #jf #j0 #j #Hf #H0
lapply (gr_pat_id_des … H0) -H0 #H destruct
/2 width=3 by ex2_intro/
qed-.

(*** at_div_id_sn *)
theorem gr_pat_div_id_sn (f):
        H_gr_pat_div 𝐢 f f 𝐢.
/3 width=6 by gr_pat_div_id_dx, gr_pat_div_comm/ qed-.

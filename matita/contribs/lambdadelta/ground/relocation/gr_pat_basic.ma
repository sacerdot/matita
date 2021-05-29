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

include "ground/relocation/gr_nat_basic.ma".

(* POSITIVE APPLICATION FOR GENERIC RELOCATION MAPS *************************)

(* Constructions with gr_basic **********************************************)

(*** at_basic_lt *)
lemma gr_pat_basic_lt (m) (n) (i):
      ninj i ≤ m → @❪i, 𝐛❨m,n❩❫ ≘ i.
#m #n #i >(npsucc_pred i) #Hmi
/2 width=1 by gr_nat_basic_lt/
qed.

(*** at_basic_ge *)
lemma gr_pat_basic_ge (m) (n) (i):
      m < ninj i → @❪i, 𝐛❨m,n❩❫ ≘ i+n.
#m #n #i >(npsucc_pred i) #Hmi <nrplus_npsucc_sn
/3 width=1 by gr_nat_basic_ge, nlt_inv_succ_dx/
qed.

(* Inversions with gr_basic *************************************************)

(*** at_basic_inv_lt *)
lemma gr_pat_basic_inv_lt (m) (n) (i) (j):
      ninj i ≤ m → @❪i, 𝐛❨m,n❩❫ ≘ j → i = j.
/3 width=4 by gr_pat_basic_lt, gr_pat_mono/ qed-.

(*** at_basic_inv_ge *)
lemma gr_pat_basic_inv_ge (m) (n) (i) (j):
      m < ninj i → @❪i, 𝐛❨m,n❩❫ ≘ j → i+n = j.
/3 width=4 by gr_pat_basic_ge, gr_pat_mono/ qed-.

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

include "ground/arith/nat_plus_rplus.ma".
include "ground/relocation/rtmap_basic_nat.ma".

(* RELOCATION MAP ***********************************************************)

(* Prioerties with application **********************************************)

lemma at_basic_lt (m) (n) (i):
      ninj i ≤ m → @❪i, 𝐁❨m,n❩❫ ≘ i.
#m #n #i >(npsucc_pred i) #Hmi
/2 width=1 by rm_nat_basic_lt/
qed.

lemma at_basic_ge (m) (n) (i):
      m < ninj i → @❪i, 𝐁❨m,n❩❫ ≘ i+n.
#m #n #i >(npsucc_pred i) #Hmi <nrplus_npsucc_sn
/3 width=1 by rm_nat_basic_ge, nlt_inv_succ_dx/
qed.

(* Inversion lemmas with application ****************************************)

lemma at_basic_inv_lt (m) (n) (i) (j):
      ninj i ≤ m → @❪i, 𝐁❨m,n❩❫ ≘ j → i = j.
/3 width=4 by at_basic_lt, at_mono/ qed-.

lemma at_basic_inv_ge (m) (n) (i) (j):
      m < ninj i → @❪i, 𝐁❨m,n❩❫ ≘ j → i+n = j.
/3 width=4 by at_basic_ge, at_mono/ qed-.

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

include "ground/arith/pnat_le.ma".
include "ground/arith/nat_rplus_succ.ma".
include "ground/arith/nat_le.ma".

(* ORDER FOR NON-NEGATIVE INTEGERS ******************************************)

(* Constructions with nrplus and ple ****************************************)

lemma ple_nrplus_bi_sn (p) (n1) (n2):
      n1 ≤ n2 → p + n1 ≤ p + n2.
#p #n1 #n2 #Hn elim Hn -Hn //
#n #Hn #IH <nrplus_succ_dx
@(ple_trans … IH) -IH //
qed.

lemma ple_nrplus_dx_dx_refl (p) (n):
      p ≤ p + n.
/2 width=1 by ple_nrplus_bi_sn/ qed.

lemma ple_nrplus_dx_dx (n) (p) (q):
      p ≤ q → p ≤ q + n.
/2 width=3 by ple_trans/ qed.

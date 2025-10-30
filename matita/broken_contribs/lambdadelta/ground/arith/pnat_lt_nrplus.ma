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

include "ground/arith/pnat_le_nrplus.ma".
include "ground/arith/pnat_lt.ma".

(* STRICT ORDER FOR POSITIVE INTEGERS ***************************************)

(* Constructions with nrplus ************************************************)

lemma plt_nrplus_bi_dx (n) (p1) (p2):
      p1 < p2 → p1+n < p2+n.
#n #p1 #p2 #Hp
@plt_i >nrplus_succ_sx
/2 width=1 by ple_nrplus_bi_dx/
qed.

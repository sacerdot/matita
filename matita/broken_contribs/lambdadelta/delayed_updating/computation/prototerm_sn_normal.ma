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

include "delayed_updating/reduction/prototerm_normal.ma".
include "delayed_updating/reduction/dbf_step_reducibles.ma".
include "delayed_updating/computation/prototerm_sn.ma".

(* STRONG NORMALIZATION FOR PROTOTERM ***************************************)

(* Constructions with normal prototerms *************************************)

lemma tsn_normal (t):
      t ϵ 𝐍𝐅 → t ϵ 𝐒𝐍.
#t1 #Ht1 @tsn_step
#t2 #r #Hr elim (tnf_inv_gen … Ht1) -Ht1
/2 width=3 by dbfs_inv_prc/
qed.

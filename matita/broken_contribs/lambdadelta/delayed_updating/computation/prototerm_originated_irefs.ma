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

include "delayed_updating/computation/dbf_steps_irefs_wfinite.ma".
include "delayed_updating/computation/prototerm_originated.ma".

(* SUBSET OF ORIGINATED PROTOTERMS ******************************************)

(* Destructions with pirc and subsets_wfinite *******************************)

lemma topc_des_pirc_wfinite (t):
      t ϵ 𝐎⁺ → 𝐈❨t❩ ϵ 𝐖𝛀.
#t2 * #t1 #rs #Ht1 #Ht12
@(dbfss_pirc_wfinite_sn … Ht12) -t2 -rs
/3 width=2 by subsets_wfinite_in/
qed-.

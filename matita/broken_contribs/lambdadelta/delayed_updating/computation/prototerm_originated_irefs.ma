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

lemma topc_des_clear_pir_wfinite (t):
      t ϵ 𝐎⁺ → ⓪𝐈❨t❩ ϵ 𝐖𝛀.
#t2 * #t1 #rs #Ht1 #Ht12
@(dbfss_clear_pir_wfinite_sx … Ht12) -t2 -rs
/4 width=2 by term_clear_wfinite, subsets_wfinite_in/
qed-.

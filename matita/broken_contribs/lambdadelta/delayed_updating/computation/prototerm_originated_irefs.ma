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

include "delayed_updating/computation/dbfrs_irefs_finite.ma".
include "delayed_updating/computation/prototerm_originated.ma".

(* SUBSET OF ORIGINATED PROTOTERMS ******************************************)

(* Destructions with pirc and subsets_finite ********************************)

lemma topc_des_pirc_finite (t):
      t ϵ 𝐎⁺ → 𝐈❨t❩ ϵ 𝛀.
#t2 * #t1 #rs #Ht1 #Ht12
@(dbfrs_pirc_finite_sn … Ht12) -t2 -rs
/3 width=2 by subsets_finite_in/
qed-.

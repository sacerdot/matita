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

include "ground/subsets/subset_listed_nimply_le.ma".
include "delayed_updating/reduction/dbfr.ma".
include "delayed_updating/reduction/dbfpr.ma".

(* DELAYED BALANCED FOCUSED PARALLEL REDUCTION ******************************)

(* Constructions with dbfr **************************************************)

lemma dbfr_dbfpr (t1) (t2) (r):
      t1 ➡𝐝𝐛𝐟[r] t2 → t1 ∥➡𝐝𝐛𝐟[❴r❵] t2.
#t1 #t2 #r * #p #b #q #n #H0 #Hb #Hq #Ht1 #Ht2 destruct
@(dbfpr_step … Hb Hq Ht1 … Ht2) //
@dbfpr_refl //
qed.
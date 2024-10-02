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

(* DELAYED BALANCED FOCUSED PARALLEL REDUCTION ******************************)

include "ground/xoa/ex_2_3.ma".
include "ground/subsets/subset_sum_lt.ma".
include "ground/subsets/subset_listed_nimply_lt.ma".
include "ground/subsets/subsets_wfinite_lt.ma".
include "delayed_updating/reduction/dbfpr.ma".

(* Main constructions *******************************************************)

lemma dbfpr_conf_wfinite (v):
      v ϵ 𝐖𝛀 → ∀t0.
      ∀t1,v1. t0 ∥➡𝐝𝐛𝐟[v1] t1 → ∀t2,v2. t0 ∥➡𝐝𝐛𝐟[v2] t2 →
      v1 ⊔ v2 ⊆ v →
      ∃∃w1,w2,t. t1 ∥➡𝐝𝐛𝐟[w1] t & t2 ∥➡𝐝𝐛𝐟[w2] t.
@subsets_wfinite_ind_lt [ /3 width=1 by eq_path_dec, eq_sum_2_dec/ ]
#v #_ #IH #t0
#t1 #v1 * -t1 -v1
[ #t1 #v1 #Ht01 #Hv1 | #u1 #t1 #v1 #p1 #b1 #q1 #n1 #Hb1 #Hq1 #Hn1 #Hv1 #Hut1 #Htu1 ]
#t2 #v2 * -t2 -v2
[1,3: #t2 #v2 #Ht02 #Hv2 |*: #u2 #t2 #v2 #p2 #b2 #q2 #n2 #Hb2 #Hq2 #Hn2 #Hv2 #Hut2 #Htu2 ]
#Hv
[ @(ex2_3_intro … v1 v2 t0) -v
  /3 width=1 by dbfpr_refl, subset_eq_sym/
| @(ex2_3_intro … v2 v1 t1) -v
  [ /2 width=1 by dbfpr_refl/
  | @(dbfpr_eq_canc_sn … Ht02) -t2
    /2 width=11 by dbfpr_step/
  ]
| @(ex2_3_intro … v2 v1 t2) -v
  [ @(dbfpr_eq_canc_sn … Ht01) -t1
    /2 width=11 by dbfpr_step/
  | /2 width=1 by dbfpr_refl/
  ]
| elim (eq_path_dec p1 p2) #Hnp12 destruct
  [
  | elim (IH … Htu1 … Htu2)
    [2: @subset_le_refl |4: skip
    |3: @(subset_lt_le_trans … Hv) -Hv
        /3 width=1 by subset_sum_lt_repl, subset_lt_nimp_single_dx_refl/
    ] #w1 #w2 #u0 #Hu10 #Hu20 -v








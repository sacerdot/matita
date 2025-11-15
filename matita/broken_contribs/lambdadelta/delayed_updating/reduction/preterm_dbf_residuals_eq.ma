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

include "ground/subsets/subset_or_eq.ma".
include "ground/subsets/subset_listed_or_eq.ma".
include "ground/subsets/subset_listed_2_or.ma".
include "delayed_updating/reduction/path_dbf_residuals_preterm.ma".
include "delayed_updating/reduction/prototerm_dbf_residuals_or.ma".

(* RESIDUALS OF A SUBSET OF DBF-REDEX POINTERS ******************************)

(* Constructions with preterm and subset_eq *********************************)

lemma term_dbfr_side_sx (t1) (t2) (r1) (r2) (p1) (p2) (b1) (b2) (q1) (q2) (n2) (n1) (x):
      t1 ϵ 𝐓 →
      r1 ϵ 𝐑❨t1,p1,b1,q1,n1❩ → r2 ϵ 𝐑❨t2,p2,b2,q2,n2❩ →
      r2 ⧸ϵ ⓪▵↑(p1◖𝗦) → ⓪(p2◖𝗦)●⓪x = r1 →
      ❴r2●⓪x❵ ⇔ ❴r1,r2●⓪x❵ /𝐝𝐛𝐟{t1} r1.
#t1 #t2 #r1 #r2 #p1 #p2 #b1 #b2 #q1 #q2 #n1 #n2 #x #Ht #Hr1 #Hr2 #Hnr2 #H0
@(subset_eq_trans … (term_dbfr_eq_repl … (subset_pair_or …)))
[2: @subset_eq_refl |3: skip ]
@(subset_eq_trans … (term_dbfr_sor …))
@(subset_eq_trans … (subset_or_eq_repl …))
[2: @subset_eq_refl |4: // |3,5: skip ]
@(subset_eq_trans ????? (subset_eq_or_dx_empty_refl …))
@(subset_eq_trans … (term_dbfr_single …))
/2 width=7 by path_dbfr_side_sx/
qed.

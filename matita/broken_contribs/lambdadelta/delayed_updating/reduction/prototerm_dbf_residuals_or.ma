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
include "ground/subsets/subset_listed_or_2.ma".
include "delayed_updating/reduction/prototerm_dbf_residuals_eq.ma".

(* RESIDUALS OF A SUBSET OF DBF-REDEX POINTERS ******************************)

(* Constructions with subset_eq and subset_or *******************************)

lemma term_dbfr_sor (u1) (u2) (r):
      (u1 /𝐝𝐛𝐟 r) ∪ (u2 /𝐝𝐛𝐟 r) ⇔ (u1 ∪ u2) /𝐝𝐛𝐟 r.
#u1 #u2 #r @conj #x *
[ * #x1 #Hx1 #Hx
  /3 width=3 by term_dbfr_mk, subset_or_in_sx/
| * #x2 #Hx2 #Hx
  /3 width=3 by term_dbfr_mk, subset_or_in_dx/
| #y * #Hy #Hx
  /3 width=3 by term_dbfr_mk, subset_or_in_dx, subset_or_in_sx/
]
qed.

(* Advanced constructions with subset_eq ************************************)

lemma term_dbfr_side_sx (r1) (p1) (p2) (b1) (b2) (q1) (q2) (n2) (n1) (x1) (x2):
      r1 ϵ 𝐑❨p1,b1,q1,n1❩ →
      p1◖𝗦 ⧸≚ 𝐫❨p2,b2,q2,n2❩ → p2◖𝗦●x1 = r1 →
      ❴𝐫❨p2,b2,q2,n2❩●x2❵ ⇔ ❴r1,𝐫❨p2,b2,q2,n2❩●x2❵ /𝐝𝐛𝐟 r1.
#r1 #p1 #p2 #b1 #b2 #q1 #q2 #n1 #n2 #x1 #x2 #Hr1 #Hnr2 #H0
@(subset_eq_trans … (term_dbfr_eq_repl … @ subset_pair_or …))
@(subset_eq_trans … (term_dbfr_sor …))
@(subset_eq_trans … (subset_or_eq_repl …))
[2: @subset_eq_refl |4: // |3,5: skip ]
@(subset_eq_trans … @ subset_eq_or_dx_empty_refl …)
@subset_or_eq_repl [ // ]
@(subset_eq_trans … (term_dbfr_single …))
/2 width=6 by path_dbfr_side_sx/
qed.

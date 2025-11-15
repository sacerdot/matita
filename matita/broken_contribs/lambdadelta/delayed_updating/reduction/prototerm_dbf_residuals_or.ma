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

include "ground/subsets/subset_or.ma".
include "delayed_updating/reduction/prototerm_dbf_residuals_eq.ma".

(* RESIDUALS OF A SUBSET OF DBF-REDEX POINTERS ******************************)

(* Constructions with subset_eq and subset_or *******************************)

lemma term_dbfr_sor (t) (u1) (u2) (r):
      (u1 /𝐝𝐛𝐟{t} r) ∪ (u2 /𝐝𝐛𝐟{t} r) ⇔ (u1 ∪ u2) /𝐝𝐛𝐟{t} r.
#t #u1 #u2 #r @conj #x *
[ * #x1 #Hx1 #Hx
  /3 width=3 by term_dbfr_mk, subset_or_in_sx/
| * #x2 #Hx2 #Hx
  /3 width=3 by term_dbfr_mk, subset_or_in_dx/
| #y * #Hy #Hx
  /3 width=3 by term_dbfr_mk, subset_or_in_dx, subset_or_in_sx/
]
qed.

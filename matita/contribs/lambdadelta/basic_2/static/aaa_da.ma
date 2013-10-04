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

include "basic_2/static/da.ma".
include "basic_2/static/aaa.ma".

(* ATONIC ARITY ASSIGNMENT FOR TERMS ****************************************)

(* Forward lemmas on degree assignment for terms ****************************)

lemma aaa_fwd_da: ∀h,g,G,L,T,A. ⦃G, L⦄ ⊢ T ⁝ A → ∃l. ⦃G, L⦄ ⊢ T ▪[h, g] l.
#h #g #G #L #T #A #H elim H -G -L -T -A
[ #G #L #k elim (deg_total … g k) /3 width=2/
| * #G #L #K [ #V | #W ] #B #i #HLK #_ * /3 width=5/
| #a #G #L #V #T #B #A #_ #_ #_ * /3 width=2/
| #a #G #L #V #T #B #A #_ #_ #_ * /3 width=2/
| #G #L #V #T #B #A #_ #_ #_ * /3 width=2/
| #G #L #W #T #A #_ #_ #_ * /3 width=2/
]
qed-.

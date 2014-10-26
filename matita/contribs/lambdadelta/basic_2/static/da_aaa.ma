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

include "basic_2/static/aaa_lift.ma".
include "basic_2/static/da.ma".

(* DEGREE ASSIGNMENT FOR TERMS **********************************************)

(* Properties on atomic arity assignment for terms **************************)

lemma aaa_da: ∀h,g,G,L,T,A. ⦃G, L⦄ ⊢ T ⁝ A → ∃d. ⦃G, L⦄ ⊢ T ▪[h, g] d.
#h #g #G #L #T #A #H elim H -G -L -T -A
[ #G #L #k elim (deg_total h g k) /3 width=2 by da_sort, ex_intro/
| * #G #L #K #V #B #i #HLK #_ * /3 width=5 by da_ldef, da_ldec, ex_intro/
| #a #G #L #V #T #B #A #_ #_ #_ * /3 width=2 by da_bind, ex_intro/
| #a #G #L #V #T #B #A #_ #_ #_ * /3 width=2 by da_bind, ex_intro/
| #G #L #V #T #B #A #_ #_ #_ * /3 width=2 by da_flat, ex_intro/
| #G #L #W #T #A #_ #_ #_ * /3 width=2 by da_flat, ex_intro/
]
qed-.

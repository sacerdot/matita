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

include "basic_2/multiple/lleq_drop.ma".
include "basic_2/static/aaa.ma".

(* ATONIC ARITY ASSIGNMENT ON TERMS *****************************************)

(* Properties on lazy equivalence for local environments ********************)

lemma lleq_aaa_trans: ∀G,L2,T,A. ⦃G, L2⦄ ⊢ T ⁝ A →
                      ∀L1. L1 ≡[T, 0] L2 → ⦃G, L1⦄ ⊢ T ⁝ A.
#G #L2 #T #A #H elim H -G -L2 -T -A /2 width=1 by aaa_sort/
[ #I #G #L2 #K2 #V2 #A #i #HLK2 #_ #IHV2 #L1 #H elim (lleq_fwd_lref_dx … H … HLK2) -L2
  [ #H elim (ylt_yle_false … H) //
  | * /3 width=5 by aaa_lref/
  ]
| #a #G #L2 #V #T #B #A #_ #_ #IHV #IHT #L1 #H elim (lleq_inv_bind_O … H) -H
  /3 width=2 by aaa_abbr/
| #a #G #L2 #V #T #B #A #_ #_ #IHV #IHT #L1 #H elim (lleq_inv_bind_O … H) -H
  /3 width=1 by aaa_abst/
| #G #L2 #V #T #B #A #_ #_ #IHV #IHT #L1 #H elim (lleq_inv_flat … H) -H
  /3 width=3 by aaa_appl/
| #G #L2 #V #T #A #_ #_ #IHV #IHT #L1 #H elim (lleq_inv_flat … H) -H
  /3 width=1 by aaa_cast/
]
qed-.

lemma aaa_lleq_conf: ∀G,L2,T,A. ⦃G, L2⦄ ⊢ T ⁝ A →
                     ∀L1. L2 ≡[T, 0] L1 → ⦃G, L1⦄ ⊢ T ⁝ A.
/3 width=3 by lleq_aaa_trans, lleq_sym/ qed-.

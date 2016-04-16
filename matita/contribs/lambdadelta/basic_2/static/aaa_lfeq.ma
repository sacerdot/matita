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

include "basic_2/static/lfeq_lreq.ma".
include "basic_2/static/aaa.ma".

(* ATONIC ARITY ASSIGNMENT ON TERMS *****************************************)

(* Properties with equivalence on referred entries **************************)

lemma lfeq_aaa_trans: ∀G,L2,T,A. ⦃G, L2⦄ ⊢ T ⁝ A →
                      ∀L1. L1 ≡[T] L2 → ⦃G, L1⦄ ⊢ T ⁝ A.
#G #L2 #T #A #H elim H -G -L2 -T -A /2 width=1 by aaa_sort/
[ #I #G #L2 #V2 #A #_ #IH #L1 #H
  elim (lfeq_inv_zero_pair_dx  … H) -H /3 width=1 by aaa_zero/
| #I #G #L2 #V2 #A #i #_ #IH #L1 #H
  elim (lfeq_inv_lref_pair_dx  … H) -H /3 width=1 by aaa_lref/
| #p #G #L2 #V #T #B #A #_ #_ #IHV #IHT #L1 #H
  elim (lfeq_inv_bind … H) -H /3 width=2 by aaa_abbr/
| #p #G #L2 #V #T #B #A #_ #_ #IHV #IHT #L1 #H
  elim (lfeq_inv_bind … H) -H /3 width=1 by aaa_abst/
| #G #L2 #V #T #B #A #_ #_ #IHV #IHT #L1 #H
  elim (lfeq_inv_flat … H) -H /3 width=3 by aaa_appl/
| #G #L2 #V #T #A #_ #_ #IHV #IHT #L1 #H
  elim (lfeq_inv_flat … H) -H /3 width=1 by aaa_cast/
]
qed-.

lemma aaa_lfeq_conf: ∀G,L2,T,A. ⦃G, L2⦄ ⊢ T ⁝ A →
                     ∀L1. L2 ≡[T] L1 → ⦃G, L1⦄ ⊢ T ⁝ A.
/3 width=3 by lfeq_aaa_trans, lfeq_sym/ qed-.

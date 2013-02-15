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

include "basic_2/static/lsubss_ssta.ma".
include "basic_2/unwind/sstas.ma".

(* ITERATED STRATIFIED STATIC TYPE ASSIGNMENT FOR TERMS *********************)

(* Properties on lenv ref for stratified type assignment ********************)

lemma lsubss_sstas_trans: ∀h,g,L2,T,U. ⦃h, L2⦄ ⊢ T •*[g] U →
                          ∀L1. h ⊢ L1 •⊑[g] L2 → ⦃h, L1⦄ ⊢ T •*[g] U.
#h #g #L2 #T #U #H @(sstas_ind_dx … H) -T // /3 width=5/
qed.

lemma lsubss_sstas_conf: ∀h,g,L1,T,U. ⦃h, L1⦄ ⊢ T •*[g] U →
                         ∀L2. h ⊢ L1 •⊑[g] L2 → ⦃h, L2⦄ ⊢ T •*[g] U.
#h #g #L2 #T #U #H @(sstas_ind_dx … H) -T // /3 width=5/
qed.

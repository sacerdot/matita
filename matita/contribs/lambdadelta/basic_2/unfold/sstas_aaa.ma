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

include "basic_2/static/ssta_aaa.ma".
include "basic_2/unfold/sstas.ma".

(* ITERATED STRATIFIED STATIC TYPE ASSIGNMENT FOR TERMS *********************)

(* Properties on atomic arity assignment for terms **************************)

lemma sstas_aaa: ∀h,g,L,T,U. ⦃h, L⦄ ⊢ T •*[g] U →
                 ∀A. L ⊢ T ⁝ A → L ⊢ U ⁝ A.
#h #g #L #T #U #H @(sstas_ind_dx … H) -T // /3 width=6/
qed.

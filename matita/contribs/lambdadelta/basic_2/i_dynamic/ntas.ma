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

include "basic_2/notation/relations/colonstar_7.ma".
include "basic_2/dynamic/cnv.ma".

(* ITERATED NATIVE TYPE ASSIGNMENT FOR TERMS ********************************)

definition ntas (h) (a) (n) (G) (L): relation term ≝ λT,U.
           ∃∃U0. ❨G,L❩ ⊢ U ![h,a] & ❨G,L❩ ⊢ T ![h,a] & ❨G,L❩ ⊢ U ➡*[h,0] U0 & ❨G,L❩ ⊢ T ➡*[h,n] U0.

interpretation "iterated native type assignment (term)"
   'ColonStar h a n G L T U = (ntas h a n G L T U).

(* Basic properties *********************************************************)

lemma ntas_intro (h) (a) (n) (G) (L):
      ∀U. ❨G,L❩ ⊢ U ![h,a] → ∀T. ❨G,L❩ ⊢ T ![h,a] →
      ∀U0. ❨G,L❩ ⊢ U ➡*[h,0] U0 → ❨G,L❩ ⊢ T ➡*[h,n] U0 → ❨G,L❩ ⊢ T :*[h,a,n] U.
/2 width=3 by ex4_intro/ qed.

lemma ntas_refl (h) (a) (G) (L):
      ∀T. ❨G,L❩ ⊢ T ![h,a] → ❨G,L❩ ⊢ T :*[h,a,0] T.
/2 width=3 by ntas_intro/ qed.

lemma ntas_sort (h) (a) (n) (G) (L):
      ∀s. ❨G,L❩ ⊢ ⋆s :*[h,a,n] ⋆((next h)^n s).
#h #a #n #G #L #s
/2 width=3 by ntas_intro, cnv_sort, cpms_sort/
qed.

lemma ntas_bind_cnv (h) (a) (n) (G) (K):
      ∀V. ❨G,K❩ ⊢ V ![h,a] →
      ∀I,T,U. ❨G,K.ⓑ[I]V❩ ⊢ T :*[h,a,n] U →
      ∀p. ❨G,K❩ ⊢ ⓑ[p,I]V.T :*[h,a,n] ⓑ[p,I]V.U.
#h #a #n #G #K #V #HV #I #T #U
* #X #HU #HT #HUX #HTX #p
/3 width=5 by ntas_intro, cnv_bind, cpms_bind_dx/
qed.

(* Basic_forward lemmas *****************************************************)

lemma ntas_fwd_cnv_sn (h) (a) (n) (G) (L):
      ∀T,U. ❨G,L❩ ⊢ T :*[h,a,n] U → ❨G,L❩ ⊢ T ![h,a].
#h #a #n #G #L #T #U
* #X #_ #HT #_ #_ //
qed-.

(* Note: this is ntas_fwd_correct_cnv *)
lemma ntas_fwd_cnv_dx (h) (a) (n) (G) (L):
      ∀T,U. ❨G,L❩ ⊢ T :*[h,a,n] U → ❨G,L❩ ⊢ U ![h,a].
#h #a #n #G #L #T #U
* #X #HU #_ #_ #_ //
qed-.

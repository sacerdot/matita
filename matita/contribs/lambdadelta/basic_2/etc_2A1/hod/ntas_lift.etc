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

include "basic_2/dynamic/nta_lift.ma".
include "basic_2/hod/ntas.ma".

(* HIGHER ORDER NATIVE TYPE ASSIGNMENT ON TERMS *****************************)

(* Advanced properties on native type assignment for terms ******************)

lemma nta_pure_ntas: ∀h,L,U,W,Y. ⦃h, L⦄ ⊢ U :* ⓛW.Y → ∀T. ⦃h, L⦄ ⊢ T : U →
                     ∀V. ⦃h, L⦄ ⊢ V : W →  ⦃h, L⦄ ⊢ ⓐV.T : ⓐV.U.
#h #L #U #W #Y #H @(ntas_ind_dx … H) -U /2 width=1/ /3 width=2/
qed.

axiom pippo: ∀h,L,T,W,Y. ⦃h, L⦄ ⊢ T :* ⓛW.Y → ∀U. ⦃h, L⦄ ⊢ T : U →
             ∃Z. ⦃h, L⦄ ⊢ U :* ⓛW.Z.
(* REQUIRES SUBJECT CONVERSION
#h #L #T #W #Y #H @(ntas_ind_dx … H) -T
[ #U #HYU
  elim (nta_fwd_correct … HYU) #U0 #HU0 
  elim (nta_inv_bind1 … HYU) #W0 #Y0 #HW0 #HY0 #HY0U
*)

(* Advanced inversion lemmas on native type assignment for terms ************)

fact nta_inv_pure1_aux: ∀h,L,Z,U. ⦃h, L⦄ ⊢ Z : U → ∀X,Y. Z = ⓐY.X →
                        ∃∃W,V,T. ⦃h, L⦄ ⊢ Y : W & ⦃h, L⦄ ⊢ X : V &
                                 L ⊢ ⓐY.V ⬌* U & ⦃h, L⦄ ⊢ V :* ⓛW.T.
#h #L #Z #U #H elim H -L -Z -U
[ #L #k #X #Y #H destruct
| #L #K #V #W #U #i #_ #_ #_ #_ #X #Y #H destruct
| #L #K #W #V #U #i #_ #_ #_ #_ #X #Y #H destruct
| #I #L #V #W #T #U #_ #_ #_ #_ #X #Y #H destruct
| #L #V #W #Z #U #HVW #HZU #_ #_ #X #Y #H destruct /2 width=7/
| #L #V #W #Z #U #HZU #_ #_ #IHUW #X #Y #H destruct
  elim (IHUW U Y ?) -IHUW // /3 width=9/
| #L #Z #U #_ #_ #X #Y #H destruct
| #L #Z #U1 #U2 #V2 #_ #HU12 #_ #IHTU1 #_ #X #Y #H destruct
  elim (IHTU1 ???) -IHTU1 [4: // |2,3: skip ] #W #V #T #HYW #HXV #HU1 #HVT
  lapply (cpcs_trans … HU1 … HU12) -U1 /2 width=7/
]
qed.

(* Basic_1: was only: ty3_gen_appl *)
lemma nta_inv_pure1: ∀h,L,Y,X,U. ⦃h, L⦄ ⊢ ⓐY.X : U →
                     ∃∃W,V,T. ⦃h, L⦄ ⊢ Y : W & ⦃h, L⦄ ⊢ X : V &
                              L ⊢ ⓐY.V ⬌* U & ⦃h, L⦄ ⊢ V :* ⓛW.T.
/2 width=3/ qed-.

axiom nta_inv_appl1: ∀h,L,Z,Y,X,U. ⦃h, L⦄ ⊢ ⓐZ.ⓛY.X : U →
                     ∃∃W. ⦃h, L⦄ ⊢ Z : Y & ⦃h, L⦄ ⊢ ⓛY.X : ⓛY.W &
                     L ⊢ ⓐZ.ⓛY.W ⬌* U.
(* REQUIRES SUBJECT REDUCTION
#h #L #Z #Y #X #U #H
elim (nta_inv_pure1 … H) -H #W #V #T #HZW #HXV #HVU #HVT
elim (nta_inv_bind1 … HXV) -HXV #Y0 #X0 #HY0 #HX0 #HX0V
lapply (cpcs_trans … (ⓐZ.ⓛY.X0) … HVU) -HVU /2 width=1/ -HX0V #HX0U
@(ex3_1_intro … HX0U) /2 width=2/
*)

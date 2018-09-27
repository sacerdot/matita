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
(*
include "basic_2/dynamic/nta_alt.ma".

(* NATIVE TYPE ASSIGNMENT ON TERMS ******************************************)

(* Advanced inversion lemmas ************************************************)

fact nta_inv_lref1_aux: ∀h,L,T,U. ⦃h, L⦄ ⊢ T : U → ∀j. T = #j →
                        (∃∃K,V,W,U0. ⇩[0, j] L ≡ K. ⓓV & ⦃h, K⦄ ⊢ V : W &
                                     ⇧[0, j + 1] W ≡ U0 & L ⊢ U0 ⬌* U
                        ) ∨
                        (∃∃K,W,V,U0. ⇩[0, j] L ≡ K. ⓛW & ⦃h, K⦄ ⊢ W : V &
                                     ⇧[0, j + 1] W ≡ U0 & L ⊢ U0 ⬌* U
                        ).
#h #L #T #U #H elim H -L -T -U
[ #L #k #j #H destruct
| #L #K #V #W #U #i #HLK #HVW #HWU #_ #j #H destruct /3 width=8/
| #L #K #W #V #U #i #HLK #HWV #HWU #_ #j #H destruct /3 width=8/
| #I #L #V #W #T #U #_ #_ #_ #_ #j #H destruct
| #L #V #W #T #U #_ #_ #_ #_ #j #H destruct
| #L #V #W #T #U #_ #_ #_ #_ #j #H destruct
| #L #T #U #_ #_ #j #H destruct
| #L #T #U1 #U2 #V2 #_ #HU12 #_ #IHTU1 #_ #j #H destruct
  elim (IHTU1 ??) -IHTU1 [4: // |2: skip ] * #K #V #W #U0 #HLK #HVW #HWU0 #HU01
  lapply (cpcs_trans … HU01 … HU12) -U1 /3 width=8/
]
qed.

(* Basic_1: was ty3_gen_lref *)
lemma nta_inv_lref1: ∀h,L,U,i. ⦃h, L⦄ ⊢ #i : U →
                     (∃∃K,V,W,U0. ⇩[0, i] L ≡ K. ⓓV & ⦃h, K⦄ ⊢ V : W &
                                  ⇧[0, i + 1] W ≡ U0 & L ⊢ U0 ⬌* U
                     ) ∨
                     (∃∃K,W,V,U0. ⇩[0, i] L ≡ K. ⓛW & ⦃h, K⦄ ⊢ W : V &
                                  ⇧[0, i + 1] W ≡ U0 & L ⊢ U0 ⬌* U
                     ).
/2 width=3/ qed-.

(* Advanced forvard lemmas **************************************************)

fact nta_fwd_pure1_aux: ∀h,L,T,U. ⦃h, L⦄ ⊢ T : U → ∀X,Y. T = ⓐY.X →
                        ∃∃V,W. ⦃h, L⦄ ⊢ Y : W & ⦃h, L⦄ ⊢ X : V & L ⊢ ⓐY.V ⬌* U.
#h #L #T #U #H elim H -L -T -U
[ #L #k #X #Y #H destruct
| #L #K #V #W #U #i #_ #_ #_ #_ #X #Y #H destruct
| #L #K #W #V #U #i #_ #_ #_ #_ #X #Y #H destruct
| #I #L #V #W #T #U #_ #_ #_ #_ #X #Y #H destruct
| #L #V #W #T #U #HVW #HTU #_ #_ #X #Y #H destruct /2 width=3/
| #L #V #W #T #U #HTU #_ #_ #IHUW #X #Y #H destruct
  elim (IHUW U Y ?) -IHUW // /2 width=3/
| #L #T #U #_ #_ #X #Y #H destruct
| #L #T #U1 #U2 #V2 #_ #HU12 #_ #IHTU1 #_ #X #Y #H destruct
  elim (IHTU1 ???) -IHTU1 [4: // |2,3: skip ] #V #W #HYW #HXV #HU1
  lapply (cpcs_trans … HU1 … HU12) -U1 /2 width=3/
]
qed.

lemma nta_fwd_pure1: ∀h,L,X,Y,U. ⦃h, L⦄ ⊢ ⓐY.X : U →
                     ∃∃V,W. ⦃h, L⦄ ⊢ Y : W & ⦃h, L⦄ ⊢ X : V & L ⊢ ⓐY.V ⬌* U.
/2 width=3/ qed-.

(* Properties on relocation *************************************************)

(* Basic_1: was: ty3_lift *)
(* Basic_2A1: was: ntaa_lift *)
lemma nta_lift: ∀h,L1,T1,U1. ⦃h, L1⦄ ⊢ T1 : U1 → ∀L2,d,e. ⇩[d, e] L2 ≡ L1 →
                ∀T2. ⇧[d, e] T1 ≡ T2 → ∀U2. ⇧[d, e] U1 ≡ U2 → ⦃h, L2⦄ ⊢ T2 : U2.
/4 width=9 by ntaa_nta, nta_ntaa, ntaa_lift/ qed.
*)

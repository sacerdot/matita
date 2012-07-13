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

include "basic_2/unfold/delift_lift.ma".
include "basic_2/static/ssta_ssta.ma".
include "basic_2/unwind/sstas_lift.ma".

(* STRATIFIED UNWIND ON TERMS ***********************************************)

(* Advanced inversion lemmas ************************************************)

lemma sstas_inv_O: ∀h,g,L,T,U. ⦃h, L⦄ ⊢ T •*[g] U →
                   ∀T0. ⦃h, L⦄ ⊢ T •[g , 0] T0 → U = T.
#h #g #L #T #U #H @(sstas_ind_alt … H) -T //
#T0 #U0 #l0 #HTU0 #_ #_ #T1 #HT01
elim (ssta_mono … HTU0 … HT01) <plus_n_Sm #H destruct
qed-.

lemma sstas_inv_S: ∀h,g,L,T,U. ⦃h, L⦄ ⊢ T •*[g] U →
                   ∀T0,l. ⦃h, L⦄ ⊢ T •[g , l+1] T0 → ⦃h, L⦄ ⊢ T0 •*[g] U.
#h #g #L #T #U #H @(sstas_ind_alt … H) -T
[ #U0 #HU0 #T #l #HUT
  elim (ssta_mono … HUT … HU0) <plus_n_Sm #H destruct
| #T0 #U0 #l0 #HTU0 #HU0 #_ #T #l #HT0
  elim (ssta_mono … HT0 … HTU0) -T0 #_ #H destruct -l0 //
]
qed-.

(* Main properties **********************************************************)

theorem sstas_mono: ∀h,g,L,T,U1. ⦃h, L⦄ ⊢ T •*[g] U1 →
                    ∀U2. ⦃h, L⦄ ⊢ T •*[g] U2 → U1 = U2.
#h #g #L #T #U1 #H @(sstas_ind_alt … H) -T
[ #T1 #HUT1 #U2 #HU12
  >(sstas_inv_O … HU12 … HUT1) -h -L -T1 -U2 //
| #T0 #U0 #l0 #HTU0 #_ #IHU01 #U2 #HU12
  lapply (sstas_inv_S … HU12 … HTU0) -T0 -l0 /2 width=1/
]
qed-.

(* More advancd inversion lemmas ********************************************)

fact sstas_inv_lref1_aux: ∀h,g,L,T,U. ⦃h, L⦄ ⊢ T •*[g] U → ∀j. T = #j →
                          ∃∃I,K,V,W. ⇩[0, j] L ≡ K. ⓑ{I}V & ⦃h, K⦄ ⊢ V •*[g] W &
                                     L ⊢ U ▼*[0, j + 1] ≡ W.
#h #g #L #T #U #H @(sstas_ind_alt … H) -T
[ #T #HUT #j #H destruct
  elim (ssta_inv_lref1 … HUT) -HUT * #K #V #W [2: #l] #HLK #HVW #HVT
  [ <plus_n_Sm #H destruct
  | /3 width=12/
  ]
| #T0 #U0 #l0 #HTU0 #HU0 #_ #j #H destruct
  elim (ssta_inv_lref1 … HTU0) -HTU0 * #K #V #W [2: #l] #HLK #HVW #HVU0
  [ #_ -HVW
    lapply (ldrop_fwd_ldrop2 … HLK) #H
    elim (sstas_inv_lift1 … HU0 … H … HVU0) -HU0 -H -HVU0 /3 width=7/
  | elim (sstas_total_S … HVW) -HVW #T #HVT #HWT
    lapply (ldrop_fwd_ldrop2 … HLK) #H
    elim (sstas_inv_lift1 … HU0 … H … HVU0) -HU0 -H -HVU0 #X #HWX
    >(sstas_mono … HWX … HWT) -X -W /3 width=7/
  ]
]
qed-.

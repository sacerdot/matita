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

include "basic_2/reduction/cpx.ma".
include "basic_2/computation/cprs.ma".

(* EXTENDED CONTEXT-SENSITIVE PARALLEL COMPUTATION ON TERMS *****************)

definition cpxs: ∀h. sd h → lenv → relation term ≝
                 λh,g. LTC … (cpx h g).

interpretation "extended context-sensitive parallel computation (term)"
   'PRedStar h g L T1 T2 = (cpxs h g L T1 T2).

(* Basic eliminators ********************************************************)

lemma cpxs_ind: ∀h,g,L,T1. ∀R:predicate term. R T1 →
                (∀T,T2. ⦃h, L⦄ ⊢ T1 ➡*[g] T → ⦃h, L⦄ ⊢ T ➡[g] T2 → R T → R T2) →
                ∀T2. ⦃h, L⦄ ⊢ T1 ➡*[g] T2 → R T2.
#h #g #L #T1 #R #HT1 #IHT1 #T2 #HT12
@(TC_star_ind … HT1 IHT1 … HT12) //
qed-.

lemma cpxs_ind_dx: ∀h,g,L,T2. ∀R:predicate term. R T2 →
                   (∀T1,T. ⦃h, L⦄ ⊢ T1 ➡[g] T → ⦃h, L⦄ ⊢ T ➡*[g] T2 → R T → R T1) →
                   ∀T1. ⦃h, L⦄ ⊢ T1 ➡*[g] T2 → R T1.
#h #g #L #T2 #R #HT2 #IHT2 #T1 #HT12
@(TC_star_ind_dx … HT2 IHT2 … HT12) //
qed-.

(* Basic properties *********************************************************)

lemma cpxs_refl: ∀h,g,L,T. ⦃h, L⦄ ⊢ T ➡*[g] T.
/2 width=1/ qed.

lemma cpx_cpxs: ∀h,g,L,T1,T2. ⦃h, L⦄ ⊢ T1 ➡[g] T2 → ⦃h, L⦄ ⊢ T1 ➡*[g] T2.
/2 width=1/ qed.

lemma cpxs_strap1: ∀h,g,L,T1,T. ⦃h, L⦄ ⊢ T1 ➡*[g] T →
                   ∀T2. ⦃h, L⦄ ⊢ T ➡[g] T2 → ⦃h, L⦄ ⊢ T1 ➡*[g] T2.
normalize /2 width=3/ qed.

lemma cpxs_strap2: ∀h,g,L,T1,T. ⦃h, L⦄ ⊢ T1 ➡[g] T →
                   ∀T2. ⦃h, L⦄ ⊢ T ➡*[g] T2 → ⦃h, L⦄ ⊢ T1 ➡*[g] T2.
normalize /2 width=3/ qed.

lemma cprs_cpxs: ∀h,g,L,T1,T2. L ⊢ T1 ➡* T2 → ⦃h, L⦄ ⊢ T1 ➡*[g] T2.
#h #g #L #T1 #T2 #H @(cprs_ind … H) -T2 // /3 width=3/
qed.

lemma cpxs_bind_dx: ∀h,g,L,V1,V2. ⦃h, L⦄ ⊢ V1 ➡[g] V2 →
                    ∀I,T1,T2. ⦃h, L. ⓑ{I}V1⦄ ⊢ T1 ➡*[g] T2 →
                    ∀a. ⦃h, L⦄ ⊢ ⓑ{a,I}V1.T1 ➡*[g] ⓑ{a,I}V2.T2.
#h #g #L #V1 #V2 #HV12 #I #T1 #T2 #HT12 #a @(cpxs_ind_dx … HT12) -T1
/3 width=1/ /3 width=3/
qed.

lemma cpxs_flat_dx: ∀h,g,L,V1,V2. ⦃h, L⦄ ⊢ V1 ➡[g] V2 →
                    ∀T1,T2. ⦃h, L⦄ ⊢ T1 ➡*[g] T2 →
                    ∀I. ⦃h, L⦄ ⊢ ⓕ{I} V1. T1 ➡*[g] ⓕ{I} V2. T2.
#h #g #L #V1 #V2 #HV12 #T1 #T2 #HT12 @(cpxs_ind … HT12) -T2 /3 width=1/ /3 width=5/
qed.

lemma cpxs_flat_sn: ∀h,g,L,T1,T2. ⦃h, L⦄ ⊢ T1 ➡[g] T2 →
                    ∀V1,V2. ⦃h, L⦄ ⊢ V1 ➡*[g] V2 →
                    ∀I. ⦃h, L⦄ ⊢ ⓕ{I} V1. T1 ➡*[g] ⓕ{I} V2. T2.
#h #g #L #T1 #T2 #HT12 #V1 #V2 #H @(cpxs_ind … H) -V2 /3 width=1/ /3 width=5/
qed.

lemma cpxs_zeta: ∀h,g,L,V,T1,T,T2. ⇧[0, 1] T2 ≡ T →
                 ⦃h, L.ⓓV⦄ ⊢ T1 ➡*[g] T → ⦃h, L⦄ ⊢ +ⓓV.T1 ➡*[g] T2.
#h #g #L #V #T1 #T #T2 #HT2 #H @(TC_ind_dx … T1 H) -T1 /3 width=3/
qed.

lemma cpxs_tau: ∀h,g,L,T1,T2. ⦃h, L⦄ ⊢ T1 ➡*[g] T2 → ∀V. ⦃h, L⦄ ⊢ ⓝV.T1 ➡*[g] T2.
#h #g #L #T1 #T2 #H elim H -T2 /2 width=3/ /3 width=1/
qed.

lemma cpxs_beta_dx: ∀h,g,a,L,V1,V2,W,T1,T2.
                    ⦃h, L⦄ ⊢ V1 ➡[g] V2 → ⦃h, L.ⓛW⦄ ⊢ T1 ➡*[g] T2 →
                    ⦃h, L⦄ ⊢ ⓐV1.ⓛ{a}W.T1 ➡*[g] ⓓ{a}V2.T2.
#h #g #a #L #V1 #V2 #W #T1 #T2 #HV12 * -T2 /3 width=1/
/4 width=6 by cpxs_strap1, cpxs_bind_dx, cpxs_flat_dx, cpx_beta/ (**) (* auto too slow without trace *)
qed.

lemma cpxs_theta_dx: ∀h,g,a,L,V1,V,V2,W1,W2,T1,T2.
                     ⦃h, L⦄ ⊢ V1 ➡[g] V → ⇧[0, 1] V ≡ V2 → ⦃h, L.ⓓW1⦄ ⊢ T1 ➡*[g] T2 →
                     ⦃h, L⦄ ⊢ W1 ➡[g] W2 → ⦃h, L⦄ ⊢ ⓐV1.ⓓ{a}W1.T1 ➡*[g] ⓓ{a}W2.ⓐV2.T2.
#h #g #a #L #V1 #V #V2 #W1 #W2 #T1 #T2 #HV1 #HV2 * -T2 [ /3 width=3/ ]
/4 width=9 by cpxs_strap1, cpxs_bind_dx, cpxs_flat_dx, cpx_theta/ (**) (* auto too slow without trace *)
qed.

(* Basic inversion lemmas ***************************************************)

lemma cpxs_inv_sort1: ∀h,g,L,U2,k. ⦃h, L⦄ ⊢ ⋆k ➡*[g] U2 →
                      ∃∃n,l. deg h g k (n+l) & U2 = ⋆((next h)^n k).
#h #g #L #U2 #k #H @(cpxs_ind … H) -U2
[ elim (deg_total h g k) #l #Hkl
  @(ex2_2_intro … 0 … Hkl) -Hkl //
| #U #U2 #_ #HU2 * #n #l #Hknl #H destruct
  elim (cpx_inv_sort1 … HU2) -HU2
  [ #H destruct /2 width=4/
  | * #l0 #Hkl0 #H destruct -l
    @(ex2_2_intro … (n+1) l0) /2 width=1/ >iter_SO //
  ]
]
qed-.

lemma cpxs_inv_appl1: ∀h,g,L,V1,T1,U2. ⦃h, L⦄ ⊢ ⓐV1.T1 ➡*[g] U2 →
                      ∨∨ ∃∃V2,T2.       ⦃h, L⦄ ⊢ V1 ➡*[g] V2 & ⦃h, L⦄ ⊢ T1 ➡*[g] T2 &
                                        U2 = ⓐV2. T2
                       | ∃∃a,V2,W,T.    ⦃h, L⦄ ⊢ V1 ➡*[g] V2 &
                                        ⦃h, L⦄ ⊢ T1 ➡*[g] ⓛ{a}W.T & ⦃h, L⦄ ⊢ ⓓ{a}V2.T ➡*[g] U2
                       | ∃∃a,V0,V2,V,T. ⦃h, L⦄ ⊢ V1 ➡*[g] V0 & ⇧[0,1] V0 ≡ V2 &
                                        ⦃h, L⦄ ⊢ T1 ➡*[g] ⓓ{a}V.T & ⦃h, L⦄ ⊢ ⓓ{a}V.ⓐV2.T ➡*[g] U2.
#h #g #L #V1 #T1 #U2 #H @(cpxs_ind … H) -U2 [ /3 width=5/ ]
#U #U2 #_ #HU2 * *
[ #V0 #T0 #HV10 #HT10 #H destruct
  elim (cpx_inv_appl1 … HU2) -HU2 *
  [ #V2 #T2 #HV02 #HT02 #H destruct /4 width=5/
  | #a #V2 #W2 #T #T2 #HV02 #HT2 #H1 #H2 destruct
    lapply (cpxs_strap1 … HV10 … HV02) -V0 /5 width=7/
  | #a #V #V2 #W0 #W2 #T #T2 #HV0 #HV2 #HW02 #HT2 #H1 #H2 destruct
    @or3_intro2 @(ex4_5_intro … HV2 HT10) /2 width=3/ /3 width=1/ (**) (* explicit constructor. /5 width=8/ is too slow because TC_transitive gets in the way *)
  ]
| /4 width=9/
| /4 width=11/
]
qed-.

lemma cpxs_inv_cast1: ∀h,g,L,W1,T1,U2. ⦃h, L⦄ ⊢ ⓝW1.T1 ➡*[g] U2 → ⦃h, L⦄ ⊢ T1 ➡*[g] U2 ∨
                      ∃∃W2,T2. ⦃h, L⦄ ⊢ W1 ➡*[g] W2 & ⦃h, L⦄ ⊢ T1 ➡*[g] T2 & U2 = ⓝW2.T2.
#h #g #L #W1 #T1 #U2 #H @(cpxs_ind … H) -U2 /3 width=5/
#U2 #U #_ #HU2 * /3 width=3/ *
#W #T #HW1 #HT1 #H destruct
elim (cpx_inv_cast1 … HU2) -HU2 /3 width=3/ *
#W2 #T2 #HW2 #HT2 #H destruct /4 width=5/
qed-.

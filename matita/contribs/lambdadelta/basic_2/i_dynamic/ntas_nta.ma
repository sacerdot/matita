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

include "basic_2/dynamic/nta_preserve.ma".
include "basic_2/i_dynamic/ntas_preserve.ma".

(* ITERATED NATIVE TYPE ASSIGNMENT FOR TERMS ********************************)

(* Properties with native type assignment for terms *************************)

lemma nta_ntas (h) (a) (G) (L):
      ∀T,U. ⦃G,L⦄ ⊢ T :[h,a] U → ⦃G,L⦄ ⊢ T :*[h,a,1] U.
#h #a #G #L #T #U #H
elim (cnv_inv_cast … H) -H /2 width=3 by ntas_intro/
qed-.

(* Inversion lemmas with native type assignment for terms *******************)

lemma ntas_inv_nta (h) (a) (G) (L):
      ∀T,U. ⦃G,L⦄ ⊢ T :*[h,a,1] U → ⦃G,L⦄ ⊢ T :[h,a] U.
#h #a #G #L #T #U
* /2 width=3 by cnv_cast/
qed-.

(* Note: this follows from ntas_inv_appl_sn *)
lemma nta_inv_appl_sn_ntas (h) (a) (G) (L) (V) (T):
      ∀X. ⦃G,L⦄ ⊢ ⓐV.T :[h,a] X →
      ∨∨ ∃∃p,W,U,U0. ad a 0 & ⦃G,L⦄ ⊢ V :[h,a] W & ⦃G,L⦄ ⊢ T :*[h,a,0] ⓛ{p}W.U0 & ⦃G,L.ⓛW⦄ ⊢ U0 :[h,a] U & ⦃G,L⦄ ⊢ ⓐV.ⓛ{p}W.U ⬌*[h] X & ⦃G,L⦄ ⊢ X ![h,a]
       | ∃∃n,p,W,U,U0. ad a (↑n) & ⦃G,L⦄ ⊢ V :[h,a] W & ⦃G,L⦄ ⊢ T :[h,a] U & ⦃G,L⦄ ⊢ U :*[h,a,n] ⓛ{p}W.U0 & ⦃G,L⦄ ⊢ ⓐV.U ⬌*[h] X & ⦃G,L⦄ ⊢ X ![h,a].
#h #a #G #L #V #T #X #H
(*
lapply (nta_ntas … H) -H #H
elim (ntas_inv_appl_sn … H) -H * #n #p #W #U #U0 #Hn #Ha #HVW #HTU #HU #HUX #HX
[ elim (eq_or_gt n) #H destruct
  [ <minus_n_O in HU; #HU -Hn
    /4 width=8 by ntas_inv_nta, ex6_4_intro, or_introl/
  | lapply (le_to_le_to_eq … Hn H) -Hn -H #H destruct
    <minus_n_n in HU; #HU
    @or_intror
    @(ex6_5_intro … Ha … HUX HX) -Ha -X
    [2,4: /2 width=2 by ntas_inv_nta/
    |6: @ntas_refl
*)
elim (cnv_inv_cast … H) -H #X0 #HX #HVT #HX0 #HTX0
elim (cnv_inv_appl … HVT) #n #p #W #U0 #Ha #HV #HT #HVW #HTU0
elim (eq_or_gt n) #Hn destruct
[ elim (cnv_fwd_cpms_abst_dx_le … HT … HTU0 1) [| // ] <minus_n_O #U #H #HU0
  lapply (cpms_appl_dx … V V … H) [ // ] -H #H
  elim (cnv_cpms_conf … HVT … HTX0 … H) -HVT -HTX0 -H <minus_n_n #X1 #HX01 #HUX1
  lapply (cpms_trans … HX0 … HX01) -X0 #HX1
  lapply (cprs_div … HUX1 … HX1) -X1 #HUX
  lapply (cnv_cpms_trans … HT … HTU0) #H
  elim (cnv_inv_bind … H) -H #_ #HU0
  /4 width=8 by cnv_cpms_ntas, cnv_cpms_nta, ex6_4_intro, or_introl/
| >(plus_minus_m_m_commutative … Hn) in HTU0; #H
  elim (cpms_inv_plus … H) -H #U #HTU #HU0
  lapply (cpms_appl_dx … V V … HTU) [ // ] #H
  elim (cnv_cpms_conf … HVT … HTX0 … H) -HVT -HTX0 -H <minus_n_n #X1 #HX01 #HUX1
  lapply (cpms_trans … HX0 … HX01) -X0 #HX1
  lapply (cprs_div … HUX1 … HX1) -X1 #HUX
  <(S_pred … Hn) in Ha; -Hn #Ha
  /5 width=10 by cnv_cpms_ntas, cnv_cpms_nta, cnv_cpms_trans, ex6_5_intro, or_intror/
]
qed-.

(*

definition ntas: sh → lenv → relation term ≝
                 λh,L. star … (nta h L).

(* Basic eliminators ********************************************************)

axiom ntas_ind_dx: ∀h,L,T2. ∀R:predicate term. R T2 →
                   (∀T1,T. ⦃h,L⦄ ⊢ T1 : T → ⦃h,L⦄ ⊢ T :* T2 → R T → R T1) →
                   ∀T1. ⦃h,L⦄ ⊢ T1 :* T2 → R T1.
(*
#h #L #T2 #R #HT2 #IHT2 #T1 #HT12
@(star_ind_dx … HT2 IHT2 … HT12) //
qed-.
*)
(* Basic properties *********************************************************)

lemma ntas_strap1: ∀h,L,T1,T,T2.
                   ⦃h,L⦄ ⊢ T1 :* T → ⦃h,L⦄  ⊢ T : T2 → ⦃h,L⦄  ⊢ T1 :* T2.
/2 width=3/ qed.

lemma ntas_strap2: ∀h,L,T1,T,T2.
                   ⦃h,L⦄  ⊢ T1 : T → ⦃h,L⦄ ⊢ T :* T2 → ⦃h,L⦄ ⊢ T1 :* T2.
/2 width=3/ qed.
*)

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

(* Advanced properties of native validity for terms *************************)

lemma cnv_appl_ntas_ge (h) (a) (G) (L):
      ∀m,n. m ≤ n → ad a n → ∀V,W. ⦃G,L⦄ ⊢ V :[h,a] W →
      ∀p,T,U. ⦃G,L⦄ ⊢ T :*[h,a,m] ⓛ{p}W.U → ⦃G,L⦄ ⊢ ⓐV.T ![h,a].
#h #a #G #L #m #n #Hmn #Hn #V #W #HVW #p #T #U #HTU
elim (cnv_inv_cast … HVW) -HVW #W0 #HW #HV #HW0 #HVW0
elim HTU -HTU #U0 #H #HT #HU0 #HTU0
elim (cnv_cpms_conf … H … HU0 0 (ⓛ{p}W0.U)) -H -HU0
[| /2 width=1 by cpms_bind/ ] -HW0 <minus_n_O #X0 #HUX0 #H
elim (cpms_inv_abst_sn … H) -H #W1 #U1 #HW01 #_ #H destruct
/3 width=13 by cnv_appl_ge, cpms_cprs_trans/
qed-.

(* Advanced inversion lemmas of native validity for terms *******************)

lemma cnv_inv_appl_ntas (h) (a) (G) (L):
      ∀V,T. ⦃G,L⦄ ⊢ ⓐV.T ![h,a] →
      ∃∃n,p,W,T,U. ad a n & ⦃G,L⦄ ⊢ V :[h,a] W & ⦃G,L⦄ ⊢ T :*[h,a,n] ⓛ{p}W.U.
#h #a #G #L #V #T #H
elim (cnv_inv_appl … H) -H #n #p #W #U #Hn #HV #HT #HVW #HTU
/3 width=9 by cnv_cpms_nta, cnv_cpms_ntas, ex3_5_intro/
qed-.

(* Properties with native type assignment for terms *************************)

lemma nta_ntas (h) (a) (G) (L):
      ∀T,U. ⦃G,L⦄ ⊢ T :[h,a] U → ⦃G,L⦄ ⊢ T :*[h,a,1] U.
#h #a #G #L #T #U #H
elim (cnv_inv_cast … H) -H /2 width=3 by ntas_intro/
qed-.

lemma ntas_step_sn (h) (a) (G) (L):
      ∀T1,T. ⦃G,L⦄ ⊢ T1 :[h,a] T →
      ∀n,T2. ⦃G,L⦄ ⊢ T :*[h,a,n] T2 → ⦃G,L⦄ ⊢ T1 :*[h,a,↑n] T2.
#h #a #G #L #T1 #T #H #n #T2 * #X2 #HT2 #HT #H1TX2 #H2TX2
elim (cnv_inv_cast … H) -H #X1 #_ #HT1 #H1TX1 #H2TX1
elim (cnv_cpms_conf … HT … H1TX1 … H2TX2) -T <minus_n_O <minus_O_n <plus_SO_sn #X #HX1 #HX2
/3 width=5 by ntas_intro, cprs_trans, cpms_trans/
qed-.

lemma ntas_step_dx (h) (a) (G) (L):
      ∀n,T1,T. ⦃G,L⦄ ⊢ T1 :*[h,a,n] T →
      ∀T2. ⦃G,L⦄ ⊢ T :[h,a] T2 → ⦃G,L⦄ ⊢ T1 :*[h,a,↑n] T2.
#h #a #G #L #n #T1 #T * #X1 #HT #HT1 #H1TX1 #H2TX1 #T2 #H
elim (cnv_inv_cast … H) -H #X2 #HT2 #_ #H1TX2 #H2TX2
elim (cnv_cpms_conf … HT … H1TX1 … H2TX2) -T <minus_n_O <minus_O_n <plus_SO_dx #X #HX1 #HX2
/3 width=5 by ntas_intro, cprs_trans, cpms_trans/
qed-.

lemma nta_appl_ntas_zero (h) (a) (G) (L): ad a 0 →
      ∀V,W. ⦃G,L⦄ ⊢ V :[h,a] W → ∀p,T,U0. ⦃G,L⦄ ⊢ T :*[h,a,0] ⓛ{p}W.U0 →
      ∀U. ⦃G,L.ⓛW⦄ ⊢ U0 :[h,a] U → ⦃G,L⦄ ⊢ ⓐV.T :[h,a] ⓐV.ⓛ{p}W.U.
#h #a #G #L #Ha #V #W #HVW #p #T #U0 #HTU0 #U #HU0
lapply (nta_fwd_cnv_dx … HVW) #HW
lapply (nta_bind_cnv … HW … HU0 p) -HW -HU0 #HU0
elim (ntas_step_dx … HTU0 … HU0) -HU0 #X #HU #_ #HUX #HTX
/4 width=9 by cnv_appl_ntas_ge, ntas_refl, cnv_cast, cpms_appl_dx/
qed.

lemma nta_appl_ntas_pos (h) (a) (n) (G) (L): ad a (↑n) →
      ∀V,W. ⦃G,L⦄ ⊢ V :[h,a] W → ∀T,U. ⦃G,L⦄ ⊢ T :[h,a] U →
      ∀p,U0. ⦃G,L⦄ ⊢ U :*[h,a,n] ⓛ{p}W.U0 → ⦃G,L⦄ ⊢ ⓐV.T :[h,a] ⓐV.U.
#h #a #n #G #L #Ha #V #W #HVW #T #U #HTU #p #U0 #HU0
elim (cnv_inv_cast … HTU) #X #_ #_ #HUX #HTX
/4 width=11 by ntas_step_sn, cnv_appl_ntas_ge, cnv_cast, cpms_appl_dx/
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
(* Note: insert here: alternate proof in ntas_nta.etc *)
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

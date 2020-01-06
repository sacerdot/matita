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

include "ground_2/xoa/ex_7_5.ma".
include "basic_2/rt_equivalence/cpcs_cprs.ma".
include "basic_2/dynamic/cnv_preserve.ma".
include "basic_2/i_dynamic/ntas.ma".

(* ITERATED NATIVE TYPE ASSIGNMENT FOR TERMS ********************************)

(* Properties based on preservation *****************************************)

lemma cnv_cpms_ntas (h) (a) (G) (L):
      ∀T. ⦃G,L⦄ ⊢ T ![h,a] → ∀n,U.⦃G,L⦄ ⊢ T ➡*[n,h] U → ⦃G,L⦄ ⊢ T :*[h,a,n] U.
/3 width=4 by ntas_intro, cnv_cpms_trans/ qed.

(* Inversion lemmas based on preservation ***********************************)

lemma ntas_inv_plus (h) (a) (n1) (n2) (G) (L):
      ∀T1,T2. ⦃G,L⦄ ⊢ T1 :*[h,a,n1+n2] T2 →
      ∃∃T0. ⦃G,L⦄ ⊢ T1 :*[h,a,n1] T0 & ⦃G,L⦄ ⊢ T0 :*[h,a,n2] T2.
#h #a #n1 #n2 #G #L #T1 #T2 * #X0 #HT2 #HT1 #H20 #H10
elim (cpms_inv_plus … H10) -H10 #T0 #H10 #H00
lapply (cnv_cpms_trans … HT1 … H10) #HT0
/3 width=6 by cnv_cpms_ntas, ntas_intro, ex2_intro/
qed-.

lemma ntas_inv_appl_sn (h) (a) (m) (G) (L) (V) (T):
      ∀X. ⦃G,L⦄ ⊢ ⓐV.T :*[h,a,m] X →
      ∨∨ ∃∃n,p,W,U,U0. n ≤ m & ad a n & ⦃G,L⦄ ⊢ V :*[h,a,1] W & ⦃G,L⦄ ⊢ T :*[h,a,n] ⓛ{p}W.U0 & ⦃G,L.ⓛW⦄ ⊢ U0 :*[h,a,m-n] U & ⦃G,L⦄ ⊢ ⓐV.ⓛ{p}W.U ⬌*[h] X & ⦃G,L⦄ ⊢ X ![h,a]
       | ∃∃n,p,W,U,U0. m ≤ n & ad a n & ⦃G,L⦄ ⊢ V :*[h,a,1] W & ⦃G,L⦄ ⊢ T :*[h,a,m] U & ⦃G,L⦄ ⊢ U :*[h,a,n-m] ⓛ{p}W.U0 & ⦃G,L⦄ ⊢ ⓐV.U ⬌*[h] X & ⦃G,L⦄ ⊢ X ![h,a].
#h #a #m #G #L #V #T #X
* #X0 #HX #HVT #HX0 #HTX0
elim (cnv_inv_appl … HVT) #n #p #W #U0 #Ha #HV #HT #HVW #HTU0
elim (le_or_ge n m) #Hnm
[ elim (cnv_fwd_cpms_abst_dx_le … HT … HTU0 … Hnm) #U #H #HU0
  lapply (cpms_appl_dx … V V … H) [ // ] -H #H
  elim (cnv_cpms_conf … HVT … HTX0 … H) -HVT -HTX0 -H <minus_n_n #X1 #HX01 #HUX1
  lapply (cpms_trans … HX0 … HX01) -X0 #HX1
  lapply (cprs_div … HUX1 … HX1) -X1 #HUX
  lapply (cnv_cpms_trans … HT … HTU0) #H
  elim (cnv_inv_bind … H) -H #_ #HU0
  /4 width=11 by cnv_cpms_ntas, ex7_5_intro, or_introl/
| >(plus_minus_m_m_commutative … Hnm) in HTU0; #H
  elim (cpms_inv_plus … H) -H #U #HTU #HU0
  lapply (cpms_appl_dx … V V … HTU) [ // ] #H
  elim (cnv_cpms_conf … HVT … HTX0 … H) -HVT -HTX0 -H <minus_n_n #X1 #HX01 #HUX1
  lapply (cpms_trans … HX0 … HX01) -X0 #HX1
  lapply (cprs_div … HUX1 … HX1) -X1 #HUX
  /5 width=11 by cnv_cpms_ntas, cnv_cpms_trans, ex7_5_intro, or_intror/
]
qed-.

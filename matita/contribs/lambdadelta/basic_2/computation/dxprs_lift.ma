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

include "basic_2/unwind/sstas_lift.ma".
include "basic_2/computation/cprs_lift.ma".
include "basic_2/computation/dxprs.ma".

(* DECOMPOSED EXTENDED PARALLEL COMPUTATION ON TERMS ************************)

(* Advanced inversion lemmas *************************************************)

lemma dxprs_inv_abst1: ∀h,g,a,L,V1,T1,U2. ⦃h, L⦄ ⊢ ⓛ{a}V1. T1 •*➡*[g] U2 →
                       ∃∃V2,T2. L ⊢ V1 ➡* V2 & ⦃h, L.ⓛV1⦄ ⊢ T1 •*➡*[g] T2 &
                                U2 = ⓛ{a}V2. T2.
#h #g #a #L #V1 #T1 #U2 * #X #H1 #H2
elim (sstas_inv_bind1 … H1) -H1 #U #HTU1 #H destruct
elim (cprs_inv_abst1 Abst V1 … H2) -H2 #V2 #T2 #HV12 #HUT2 #H destruct /3 width=5/
qed-.

(* Advanced properties ******************************************************)

lemma ssta_cprs_dxprs: ∀h,g,L,T1,T,T2,l. ⦃h, L⦄ ⊢ T1 •[g, l+1] T → 
                       L ⊢ T ➡* T2 → ⦃h, L⦄ ⊢ T1 •*➡*[g] T2.
/3 width=3/ qed.

(* Relocation properties ****************************************************)

lemma dxprs_lift: ∀L,K,d,e. ⇩[d, e] L ≡ K → ∀T1,U1. ⇧[d, e] T1 ≡ U1 →
                  ∀h,g,T2. ⦃h, K⦄ ⊢ T1 •*➡*[g] T2 → ∀U2. ⇧[d, e] T2 ≡ U2 →
                  ⦃h, L⦄ ⊢ U1 •*➡*[g] U2.
#L #K #d #e #HLK #T1 #U1 #HTU1 #h #g #T2 * #T
elim (lift_total T d e) /3 width=11/
qed.

lemma dxprs_inv_lift1: ∀L,K,d,e. ⇩[d, e] L ≡ K →
                       ∀T1,U1. ⇧[d, e] T1 ≡ U1 → ∀h,g,U2. ⦃h, L⦄ ⊢ U1 •*➡*[g] U2 →
                       ∃∃T2. ⇧[d, e] T2 ≡ U2 & ⦃h, K⦄ ⊢ T1 •*➡*[g] T2.
#L #K #d #e #HLK #T1 #U1 #HTU1 #h #g #U2 * #U #HU1 #HU2
elim (sstas_inv_lift1 … HU1 … HLK … HTU1) -U1 #T #HT1 #HTU
elim (cprs_inv_lift1 … HLK … HTU … HU2) -U -L /3 width=5/
qed-.

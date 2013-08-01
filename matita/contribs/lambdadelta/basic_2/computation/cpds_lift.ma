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

include "basic_2/unfold/sstas_lift.ma".
include "basic_2/computation/cprs_lift.ma".
include "basic_2/computation/cpds.ma".

(* DECOMPOSED EXTENDED PARALLEL COMPUTATION ON TERMS ************************)

(* Relocation properties ****************************************************)

lemma cpds_lift: ∀L,K,d,e. ⇩[d, e] L ≡ K → ∀T1,U1. ⇧[d, e] T1 ≡ U1 →
                 ∀h,g,T2. ⦃h, K⦄ ⊢ T1 •*➡*[h, g] T2 → ∀U2. ⇧[d, e] T2 ≡ U2 →
                 ⦃G, L⦄ ⊢ U1 •*➡*[h, g] U2.
#L #K #d #e #HLK #T1 #U1 #HTU1 #h #g #T2 * #T
elim (lift_total T d e) /3 width=11/
qed.

lemma cpds_inv_lift1: ∀L,K,d,e. ⇩[d, e] L ≡ K →
                      ∀T1,U1. ⇧[d, e] T1 ≡ U1 → ∀h,g,U2. ⦃G, L⦄ ⊢ U1 •*➡*[h, g] U2 →
                      ∃∃T2. ⇧[d, e] T2 ≡ U2 & ⦃h, K⦄ ⊢ T1 •*➡*[h, g] T2.
#L #K #d #e #HLK #T1 #U1 #HTU1 #h #g #U2 * #U #HU1 #HU2
elim (sstas_inv_lift1 … HU1 … HLK … HTU1) -U1 #T #HT1 #HTU
elim (cprs_inv_lift1 … HU2 … HLK … HTU) -U -L /3 width=5/
qed-.

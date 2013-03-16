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

include "basic_2/unwind/sstas_sstas.ma".
include "basic_2/computation/cprs_lfprs.ma".
include "basic_2/computation/dxprs.ma".

(* DECOMPOSED EXTENDED PARALLEL COMPUTATION ON TERMS ************************)

(* Advanced properties ******************************************************)

lemma dxprs_cprs_trans: ∀h,g,L,T1,T,T2.
                        ⦃h, L⦄ ⊢ T1 •*➡*[g] T → L ⊢ T ➡* T2 → ⦃h, L⦄ ⊢ T1 •*➡*[g] T2.
#h #g #L #T1 #T #T2 * #T0 #HT10 #HT0 #HT2
lapply (cprs_trans … HT0 … HT2) -T /2 width=3/
qed-.

lemma sstas_dxprs_trans: ∀h,g,L,T1,T,T2.
                         ⦃h, L⦄ ⊢ T1 •*[g] T → ⦃h, L⦄ ⊢ T •*➡*[g] T2 → ⦃h, L⦄ ⊢ T1 •*➡*[g] T2.
#h #g #L #T1 #T #T2 #HT1 * #T0 #HT0 #HT02
lapply (sstas_trans … HT1 … HT0) -T /2 width=3/
qed-.

(* Advanced inversion lemmas ************************************************)

lemma dxprs_inv_abbr_abst: ∀h,g,a1,a2,L,V1,W2,T1,T2. ⦃h, L⦄ ⊢ ⓓ{a1}V1.T1 •*➡*[g] ⓛ{a2}W2.T2 →
                           ∃∃T. ⦃h, L.ⓓV1⦄ ⊢ T1 •*➡*[g] T & ⇧[0, 1] ⓛ{a2}W2.T2 ≡ T & a1 = true.
#h #g #a1 #a2 #L #V1 #W2 #T1 #T2 * #X #H1 #H2
elim (sstas_inv_bind1 … H1) -H1 #U1 #HTU1 #H destruct
elim (cprs_inv_abbr1 … H2) -H2 *
[ #V2 #U2 #HV12 #HU12 #H destruct
| /3 width=3/
]
qed-.

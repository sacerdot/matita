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

include "basic_2/notation/relations/lazypredsnstar_7.ma".
include "basic_2/reduction/llpx.ma".

(* LAZY SN EXTENDED PARALLEL COMPUTATION ON LOCAL ENVIRONMENTS **************)

definition llpxs: ∀h. sd h → genv → relation4 ynat term lenv lenv ≝
                  λh,g,G,d. LTC … (llpx h g G d).

interpretation "lazy extended parallel computation (local environment, sn variant)"
   'LazyPRedSnStar G L1 L2 h g T d = (llpxs h g G d T L1 L2).

(* Basic eliminators ********************************************************)

lemma llpxs_ind: ∀h,g,G,L1,T,d. ∀R:predicate lenv. R L1 →
                 (∀L,L2. ⦃G, L1⦄ ⊢ ➡*[h, g, T, d] L → ⦃G, L⦄ ⊢ ➡[h, g, T, d] L2 → R L → R L2) →
                 ∀L2. ⦃G, L1⦄ ⊢ ➡*[h, g, T, d] L2 → R L2.
#h #g #G #L1 #T #d #R #HL1 #IHL1 #L2 #HL12
@(TC_star_ind … HL1 IHL1 … HL12) //
qed-.

lemma llpxs_ind_dx: ∀h,g,G,L2,T,d. ∀R:predicate lenv. R L2 →
                    (∀L1,L. ⦃G, L1⦄ ⊢ ➡[h, g, T, d] L → ⦃G, L⦄ ⊢ ➡*[h, g, T, d] L2 → R L → R L1) →
                    ∀L1. ⦃G, L1⦄ ⊢ ➡*[h, g, T, d] L2 → R L1.
#h #g #G #L2 #T #d #R #HL2 #IHL2 #L1 #HL12
@(TC_star_ind_dx … HL2 IHL2 … HL12) //
qed-.

(* Basic properties *********************************************************)

lemma llpx_llpxs: ∀h,g,G,L1,L2,T,d. ⦃G, L1⦄ ⊢ ➡[h, g, T, d] L2 → ⦃G, L1⦄ ⊢ ➡*[h, g, T, d] L2.
normalize /2 width=1 by inj/ qed.

lemma llpxs_refl: ∀h,g,G,L,T,d. ⦃G, L⦄ ⊢ ➡*[h, g, T, d] L.
/2 width=1 by llpx_llpxs/ qed.

lemma llpxs_strap1: ∀h,g,G,L1,L,L2,T,d. ⦃G, L1⦄ ⊢ ➡*[h, g, T, d] L → ⦃G, L⦄ ⊢ ➡[h, g, T, d] L2 → ⦃G, L1⦄ ⊢ ➡*[h, g, T, d] L2.
normalize /2 width=3 by step/ qed.

lemma llpxs_strap2: ∀h,g,G,L1,L,L2,T,d. ⦃G, L1⦄ ⊢ ➡[h, g, T, d] L → ⦃G, L⦄ ⊢ ➡*[h, g, T, d] L2 → ⦃G, L1⦄ ⊢ ➡*[h, g, T, d] L2.
normalize /2 width=3 by TC_strap/ qed.

(* Basic forward lemmas *****************************************************)

lemma llpxs_fwd_length: ∀h,g,G,L1,L2,T,d. ⦃G, L1⦄ ⊢ ➡*[h, g, T, d] L2 → |L1| = |L2|.
#h #g #G #L1 #L2 #T #d #H @(llpxs_ind … H) -L2
/3 width=8 by llpx_fwd_length, trans_eq/
qed-.

(* Note: this might be moved *)
lemma llpxs_fwd_bind_sn: ∀h,g,a,I,G,L1,L2,V,T,d. ⦃G, L1⦄ ⊢ ➡*[h, g, ⓑ{a,I}V.T, d] L2 →
                         ⦃G, L1⦄ ⊢ ➡*[h, g, V, d] L2.
#h #g #a #I #G #L1 #L2 #V #T #d #H @(llpxs_ind … H) -L2
/3 width=6 by llpx_fwd_bind_sn, llpxs_strap1/
qed-.

(* Note: this might be moved *)
lemma llpxs_fwd_bind_dx: ∀h,g,a,I,G,L1,L2,V,T,d. ⦃G, L1⦄ ⊢ ➡*[h, g, ⓑ{a,I}V.T, d] L2 →
                         ⦃G, L1.ⓑ{I}V⦄ ⊢ ➡*[h, g, T, ⫯d] L2.ⓑ{I}V.
#h #g #a #I #G #L1 #L2 #V #T #d #H @(llpxs_ind … H) -L2
/3 width=6 by llpx_fwd_bind_dx, llpxs_strap1/
qed-.

(* Note: this might be moved *)
lemma llpxs_fwd_flat_sn: ∀h,g,I,G,L1,L2,V,T,d. ⦃G, L1⦄ ⊢ ➡*[h, g, ⓕ{I}V.T, d] L2 →
                         ⦃G, L1⦄ ⊢ ➡*[h, g, V, d] L2.
#h #g #I #G #L1 #L2 #V #T #d #H @(llpxs_ind … H) -L2
/3 width=6 by llpx_fwd_flat_sn, llpxs_strap1/
qed-.

(* Note: this might be moved *)
lemma llpxs_fwd_flat_dx: ∀h,g,I,G,L1,L2,V,T,d. ⦃G, L1⦄ ⊢ ➡*[h, g, ⓕ{I}V.T, d] L2 →
                         ⦃G, L1⦄ ⊢ ➡*[h, g, T, d] L2.
#h #g #I #G #L1 #L2 #V #T #d #H @(llpxs_ind … H) -L2
/3 width=6 by llpx_fwd_flat_dx, llpxs_strap1/
qed-.

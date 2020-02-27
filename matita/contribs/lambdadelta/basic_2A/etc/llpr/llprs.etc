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

include "basic_2/notation/relations/lazypredsnstar_5.ma".
include "basic_2/reduction/llpr.ma".

(* LAZY SN PARALLEL COMPUTATION ON LOCAL ENVIRONMENTS ***********************)

definition llprs: genv → relation4 ynat term lenv lenv ≝
                  λG,d. LTC … (llpr G d).

interpretation "lazy parallel computation (local environment, sn variant)"
   'LazyPRedSnStar G L1 L2 T d = (llprs G d T L1 L2).

(* Basic eliminators ********************************************************)

lemma llprs_ind: ∀G,L1,T,d. ∀R:predicate lenv. R L1 →
                 (∀L,L2. ⦃G, L1⦄ ⊢ ➡*[T, d] L → ⦃G, L⦄ ⊢ ➡[T, d] L2 → R L → R L2) →
                 ∀L2. ⦃G, L1⦄ ⊢ ➡*[T, d] L2 → R L2.
#G #L1 #T #d #R #HL1 #IHL1 #L2 #HL12
@(TC_star_ind … HL1 IHL1 … HL12) //
qed-.

lemma llprs_ind_dx: ∀G,L2,T,d. ∀R:predicate lenv. R L2 →
                    (∀L1,L. ⦃G, L1⦄ ⊢ ➡[T, d] L → ⦃G, L⦄ ⊢ ➡*[T, d] L2 → R L → R L1) →
                    ∀L1. ⦃G, L1⦄ ⊢ ➡*[T, d] L2 → R L1.
#G #L2 #T #d #R #HL2 #IHL2 #L1 #HL12
@(TC_star_ind_dx … HL2 IHL2 … HL12) //
qed-.

(* Basic properties *********************************************************)

lemma lpr_llprs: ∀G,L1,L2,T,d. ⦃G, L1⦄ ⊢ ➡[T, d] L2 → ⦃G, L1⦄ ⊢ ➡*[T, d] L2.
/2 width=1 by inj/ qed.

lemma llprs_refl: ∀G,L,T,d. ⦃G, L⦄ ⊢ ➡*[T, d] L.
/2 width=1 by lpr_llprs/ qed.

lemma llprs_strap1: ∀G,L1,L,L2,T,d. ⦃G, L1⦄ ⊢ ➡*[T, d] L → ⦃G, L⦄ ⊢ ➡[T, d] L2 → ⦃G, L1⦄ ⊢ ➡*[T, d] L2.
normalize /2 width=3 by step/ qed-.

lemma llprs_strap2: ∀G,L1,L,L2,T,d. ⦃G, L1⦄ ⊢ ➡[T, d] L → ⦃G, L⦄ ⊢ ➡*[T, d] L2 → ⦃G, L1⦄ ⊢ ➡*[T, d] L2.
normalize /2 width=3 by TC_strap/ qed-.

(* Basic forward lemmas *****************************************************)

lemma llprs_fwd_length: ∀G,L1,L2,T,d. ⦃G, L1⦄ ⊢ ➡*[T, d] L2 → |L1| = |L2|.
#G #L1 #L2 #T #d #H @(llprs_ind … H) -L2
/3 width=6 by llpr_fwd_length, trans_eq/
qed-.

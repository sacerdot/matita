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

include "basic_2A/notation/relations/nativevalid_6.ma".
include "basic_2A/equivalence/scpes.ma".
include "basic_2A/dynamic/snv.ma".

(* STRATIFIED HIGHER NATIVE VALIDITY FOR TERMS ******************************)

inductive shnv (h) (g) (d1) (G) (L): predicate term ≝
| shnv_cast: ∀U,T. ⦃G, L⦄ ⊢ U ¡[h, g] → ⦃G, L⦄ ⊢ T ¡[h, g] →
             (∀d2. d2 ≤ d1 → ⦃G, L⦄ ⊢ U •*⬌*[h, g, d2, d2+1] T) →
             shnv h g d1 G L (ⓝU.T)
.

interpretation "stratified higher native validity (term)"
   'NativeValid h g d G L T = (shnv h g d G L T).

(* Basic inversion lemmas ***************************************************)

fact shnv_inv_cast_aux: ∀h,g,G,L,X,d1. ⦃G, L⦄ ⊢ X ¡[h, g, d1] → ∀U,T. X = ⓝU.T →
                        ∧∧ ⦃G, L⦄ ⊢ U ¡[h, g] & ⦃G, L⦄ ⊢ T ¡[h, g]
                         & (∀d2. d2 ≤ d1 → ⦃G, L⦄ ⊢ U •*⬌*[h, g, d2, d2+1] T).
#h #g #G #L #X #d1 * -X
#U #T #HU #HT #HUT #U1 #T1 #H destruct /3 width=1 by and3_intro/
qed-.

lemma shnv_inv_cast: ∀h,g,G,L,U,T,d1. ⦃G, L⦄ ⊢ ⓝU.T ¡[h, g, d1] →
                     ∧∧ ⦃G, L⦄ ⊢ U ¡[h, g] & ⦃G, L⦄ ⊢ T ¡[h, g]
                      & (∀d2. d2 ≤ d1 → ⦃G, L⦄ ⊢ U •*⬌*[h, g, d2, d2+1] T).
/2 width=3 by shnv_inv_cast_aux/ qed-.

lemma shnv_inv_snv: ∀h,g,G,L,T,d. ⦃G, L⦄ ⊢ T ¡[h, g, d] → ⦃G, L⦄ ⊢ T ¡[h, g].
#h #g #G #L #T #d * -T
#U #T #HU #HT #HUT elim (HUT 0) -HUT /2 width=3 by snv_cast/
qed-.

(* Basic properties *********************************************************)

lemma snv_shnv_cast: ∀h,g,G,L,U,T. ⦃G, L⦄ ⊢ ⓝU.T ¡[h, g] → ⦃G, L⦄ ⊢ ⓝU.T ¡[h, g, 0].
#h #g #G #L #U #T #H elim (snv_inv_cast … H) -H
#U0 #HU #HT #HU0 #HTU0 @shnv_cast // -HU -HT
#d #H <(le_n_O_to_eq … H) -d /2 width=3 by scpds_div/
qed.

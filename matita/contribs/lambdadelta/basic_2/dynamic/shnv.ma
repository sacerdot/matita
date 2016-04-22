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

include "basic_2/notation/relations/nativevalid_6.ma".
include "basic_2/equivalence/scpes.ma".
include "basic_2/dynamic/snv.ma".

(* STRATIFIED HIGHER NATIVE VALIDITY FOR TERMS ******************************)

inductive shnv (h) (o) (d1) (G) (L): predicate term ≝
| shnv_cast: ∀U,T. ⦃G, L⦄ ⊢ U ¡[h, o] → ⦃G, L⦄ ⊢ T ¡[h, o] →
             (∀d2. d2 ≤ d1 → ⦃G, L⦄ ⊢ U •*⬌*[h, o, d2, d2+1] T) →
             shnv h o d1 G L (ⓝU.T)
.

interpretation "stratified higher native validity (term)"
   'NativeValid h o d G L T = (shnv h o d G L T).

(* Basic inversion lemmas ***************************************************)

fact shnv_inv_cast_aux: ∀h,o,G,L,X,d1. ⦃G, L⦄ ⊢ X ¡[h, o, d1] → ∀U,T. X = ⓝU.T →
                        ∧∧ ⦃G, L⦄ ⊢ U ¡[h, o] & ⦃G, L⦄ ⊢ T ¡[h, o]
                         & (∀d2. d2 ≤ d1 → ⦃G, L⦄ ⊢ U •*⬌*[h, o, d2, d2+1] T).
#h #o #G #L #X #d1 * -X
#U #T #HU #HT #HUT #U1 #T1 #H destruct /3 width=1 by and3_intro/
qed-.

lemma shnv_inv_cast: ∀h,o,G,L,U,T,d1. ⦃G, L⦄ ⊢ ⓝU.T ¡[h, o, d1] →
                     ∧∧ ⦃G, L⦄ ⊢ U ¡[h, o] & ⦃G, L⦄ ⊢ T ¡[h, o]
                      & (∀d2. d2 ≤ d1 → ⦃G, L⦄ ⊢ U •*⬌*[h, o, d2, d2+1] T).
/2 width=3 by shnv_inv_cast_aux/ qed-.

lemma shnv_inv_snv: ∀h,o,G,L,T,d. ⦃G, L⦄ ⊢ T ¡[h, o, d] → ⦃G, L⦄ ⊢ T ¡[h, o].
#h #o #G #L #T #d * -T
#U #T #HU #HT #HUT elim (HUT 0) -HUT /2 width=3 by snv_cast/
qed-.

(* Basic properties *********************************************************)

lemma snv_shnv_cast: ∀h,o,G,L,U,T. ⦃G, L⦄ ⊢ ⓝU.T ¡[h, o] → ⦃G, L⦄ ⊢ ⓝU.T ¡[h, o, 0].
#h #o #G #L #U #T #H elim (snv_inv_cast … H) -H
#U0 #HU #HT #HU0 #HTU0 @shnv_cast // -HU -HT
#d #H <(le_n_O_to_eq … H) -d /2 width=3 by scpds_div/
qed.

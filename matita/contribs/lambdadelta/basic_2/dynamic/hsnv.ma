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
include "basic_2/equivalence/cpes.ma".
include "basic_2/dynamic/snv.ma".

(* HIGHER ORDER STRATIFIED NATIVE VALIDITY FOR TERMS ************************)

inductive hsnv (h) (g) (l1) (G) (L): predicate term ≝
| hsnv_cast: ∀U,T. ⦃G, L⦄ ⊢ U ¡[h, g] → ⦃G, L⦄ ⊢ T ¡[h, g] →
             (∀l2. l2 ≤ l1 → ⦃G, L⦄ ⊢ U •*⬌*[h, g, l2, l2+1] T) →
             hsnv h g l1 G L (ⓝU.T)
.

interpretation "higher order stratified native validity (term)"
   'NativeValid h g l G L T = (hsnv h g l G L T).

(* Basic inversion lemmas ***************************************************)

fact hsnv_inv_cast_aux: ∀h,g,G,L,X,l1. ⦃G, L⦄ ⊢ X ¡[h, g, l1] → ∀U,T. X = ⓝU.T →
                        ∧∧ ⦃G, L⦄ ⊢ U ¡[h, g] & ⦃G, L⦄ ⊢ T ¡[h, g]
                         & (∀l2. l2 ≤ l1 → ⦃G, L⦄ ⊢ U •*⬌*[h, g, l2, l2+1] T).
#h #g #G #L #X #l1 * -X
#U #T #HU #HT #HUT #U1 #T1 #H destruct /3 width=1 by and3_intro/
qed-.

lemma hsnv_inv_cast: ∀h,g,G,L,U,T,l1. ⦃G, L⦄ ⊢ ⓝU.T ¡[h, g, l1] →
                     ∧∧ ⦃G, L⦄ ⊢ U ¡[h, g] & ⦃G, L⦄ ⊢ T ¡[h, g]
                      & (∀l2. l2 ≤ l1 → ⦃G, L⦄ ⊢ U •*⬌*[h, g, l2, l2+1] T).
/2 width=3 by hsnv_inv_cast_aux/ qed-.

lemma hsnv_inv_snv: ∀h,g,G,L,T,l. ⦃G, L⦄ ⊢ T ¡[h, g, l] → ⦃G, L⦄ ⊢ T ¡[h, g].
#h #g #G #L #T #l * -T
#U #T #HU #HT #HUT elim (HUT 0) -HUT
/3 width=3 by snv_cast, cpds_fwd_cprs/
qed-.

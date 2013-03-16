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

include "basic_2/static/ssta_ssta.ma".
include "basic_2/unwind/sstas.ma".

(* ITERATED STRATIFIED STATIC TYPE ASSIGNMENT FOR TERMS *********************)

(* Advanced inversion lemmas ************************************************)

lemma sstas_inv_O: ∀h,g,L,T,U. ⦃h, L⦄ ⊢ T •*[g] U →
                   ∀T0. ⦃h, L⦄ ⊢ T •[g] ⦃0, T0⦄ → U = T.
#h #g #L #T #U #H @(sstas_ind_dx … H) -T //
#T0 #U0 #l0 #HTU0 #_ #_ #T1 #HT01
elim (ssta_mono … HTU0 … HT01) <plus_n_Sm #H destruct
qed-.

(* Advanced properties ******************************************************)

lemma sstas_strip: ∀h,g,L,T,U1. ⦃h, L⦄ ⊢ T •*[g] U1 →
                   ∀U2,l. ⦃h, L⦄ ⊢ T •[g] ⦃l, U2⦄ →
                   T = U1 ∨ ⦃h, L⦄ ⊢ U2 •*[g] U1.
#h #g #L #T #U1 #H1 @(sstas_ind_dx … H1) -T /2 width=1/
#T #U #l0 #HTU #HU1 #_ #U2 #l #H2
elim (ssta_mono … H2 … HTU) -H2 -HTU #H1 #H2 destruct /2 width=1/
qed-.

(* Main properties **********************************************************)

theorem sstas_trans: ∀h,g,L,T1,U. ⦃h, L⦄ ⊢ T1 •*[g] U →
                     ∀T2. ⦃h, L⦄ ⊢ U •*[g] T2 → ⦃h, L⦄ ⊢ T1 •*[g] T2.
/2 width=3/ qed-.

theorem sstas_conf: ∀h,g,L,T,U1. ⦃h, L⦄ ⊢ T •*[g] U1 →
                    ∀U2. ⦃h, L⦄ ⊢ T •*[g] U2 →
                   ⦃h, L⦄ ⊢ U1 •*[g] U2 ∨ ⦃h, L⦄ ⊢ U2 •*[g] U1.
#h #g #L #T #U1 #H1 @(sstas_ind_dx … H1) -T /2 width=1/
#T #U #l #HTU #HU1 #IHU1 #U2 #H2
elim (sstas_strip … H2 … HTU) #H destruct
[ -H2 -IHU1 /3 width=4/
| -T /2 width=1/
]
qed-.

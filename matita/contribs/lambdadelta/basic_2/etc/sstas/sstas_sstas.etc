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
include "basic_2/unfold/sstas.ma".

(* ITERATED STRATIFIED STATIC TYPE ASSIGNMENT FOR TERMS *********************)

(* Advanced inversion lemmas ************************************************)

lemma sstas_inv_O: ∀h,g,G,L,T,U. ⦃G, L⦄ ⊢ T •*[h, g] U →
                   ∀T0. ⦃G, L⦄ ⊢ T •[h, g] ⦃0, T0⦄ → U = T.
#h #g #G #L #T #U #H @(sstas_ind_dx … H) -T //
#T0 #U0 #l0 #HTU0 #_ #_ #T1 #HT01
elim (ssta_mono … HTU0 … HT01) <plus_n_Sm #H destruct
qed-.

(* Advanced properties ******************************************************)

lemma sstas_strip: ∀h,g,G,L,T,U1. ⦃G, L⦄ ⊢ T •*[h, g] U1 →
                   ∀U2,l. ⦃G, L⦄ ⊢ T •[h, g] ⦃l, U2⦄ →
                   T = U1 ∨ ⦃G, L⦄ ⊢ U2 •*[h, g] U1.
#h #g #G #L #T #U1 #H1 @(sstas_ind_dx … H1) -T /2 width=1/
#T #U #l0 #HTU #HU1 #_ #U2 #l #H2
elim (ssta_mono … H2 … HTU) -H2 -HTU #H1 #H2 destruct /2 width=1/
qed-.

(* Main properties **********************************************************)

theorem sstas_trans: ∀h,g,G,L,T1,U. ⦃G, L⦄ ⊢ T1 •*[h, g] U →
                     ∀T2. ⦃G, L⦄ ⊢ U •*[h, g] T2 → ⦃G, L⦄ ⊢ T1 •*[h, g] T2.
/2 width=3/ qed-.

theorem sstas_conf: ∀h,g,G,L,T,U1. ⦃G, L⦄ ⊢ T •*[h, g] U1 →
                    ∀U2. ⦃G, L⦄ ⊢ T •*[h, g] U2 →
                   ⦃G, L⦄ ⊢ U1 •*[h, g] U2 ∨ ⦃G, L⦄ ⊢ U2 •*[h, g] U1.
#h #g #G #L #T #U1 #H1 @(sstas_ind_dx … H1) -T /2 width=1/
#T #U #l #HTU #HU1 #IHU1 #U2 #H2
elim (sstas_strip … H2 … HTU) #H destruct
[ -H2 -IHU1 /3 width=4/
| -T /2 width=1/
]
qed-.

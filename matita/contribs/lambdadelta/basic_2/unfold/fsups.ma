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

include "basic_2/unfold/fsupp.ma".

(* STAR-ITERATED SUPCLOSURE *************************************************)

definition fsups: bi_relation lenv term ≝ bi_star … fsup.

interpretation "star-iterated structural successor (closure)"
   'SupTermStar L1 T1 L2 T2 = (fsups L1 T1 L2 T2).

(* Basic eliminators ********************************************************)

lemma fsups_ind: ∀L1,T1. ∀R:relation2 lenv term. R L1 T1 →
                 (∀L,L2,T,T2. ⦃L1, T1⦄ ⊃* ⦃L, T⦄ → ⦃L, T⦄ ⊃ ⦃L2, T2⦄ → R L T → R L2 T2) →
                 ∀L2,T2. ⦃L1, T1⦄ ⊃* ⦃L2, T2⦄ → R L2 T2.
#L1 #T1 #R #IH1 #IH2 #L2 #T2 #H
@(bi_star_ind … IH1 IH2 ? ? H)
qed-.

lemma fsups_ind_dx: ∀L2,T2. ∀R:relation2 lenv term. R L2 T2 →
                    (∀L1,L,T1,T. ⦃L1, T1⦄ ⊃ ⦃L, T⦄ → ⦃L, T⦄ ⊃* ⦃L2, T2⦄ → R L T → R L1 T1) →
                    ∀L1,T1. ⦃L1, T1⦄ ⊃* ⦃L2, T2⦄ → R L1 T1.
#L2 #T2 #R #IH1 #IH2 #L1 #T1 #H
@(bi_star_ind_dx … IH1 IH2 ? ? H)
qed-.

(* Basic properties *********************************************************)

lemma fsups_refl: bi_reflexive … fsups.
/2 width=1/ qed.

lemma fsupp_fsups: ∀L1,L2,T1,T2. ⦃L1, T1⦄ ⊃+ ⦃L2, T2⦄ → ⦃L1, T1⦄ ⊃* ⦃L2, T2⦄.
/2 width=1/ qed.

lemma fsup_fsups: ∀L1,L2,T1,T2. ⦃L1, T1⦄ ⊃ ⦃L2, T2⦄ → ⦃L1, T1⦄ ⊃* ⦃L2, T2⦄.
/2 width=1/ qed.

lemma fsups_strap1: ∀L1,L,L2,T1,T,T2. ⦃L1, T1⦄ ⊃* ⦃L, T⦄ → ⦃L, T⦄ ⊃ ⦃L2, T2⦄ →
                    ⦃L1, T1⦄ ⊃* ⦃L2, T2⦄.
/2 width=4/ qed.

lemma fsups_strap2: ∀L1,L,L2,T1,T,T2. ⦃L1, T1⦄ ⊃ ⦃L, T⦄ → ⦃L, T⦄ ⊃* ⦃L2, T2⦄ →
                    ⦃L1, T1⦄ ⊃* ⦃L2, T2⦄.
/2 width=4/ qed.

lemma fsups_fsupp_fsupp: ∀L1,L,L2,T1,T,T2. ⦃L1, T1⦄ ⊃* ⦃L, T⦄ →
                         ⦃L, T⦄ ⊃+ ⦃L2, T2⦄ → ⦃L1, T1⦄ ⊃+ ⦃L2, T2⦄.
/2 width=4/ qed.

lemma fsupp_fsups_fsupp: ∀L1,L,L2,T1,T,T2. ⦃L1, T1⦄ ⊃+ ⦃L, T⦄ →
                         ⦃L, T⦄ ⊃* ⦃L2, T2⦄ → ⦃L1, T1⦄ ⊃+ ⦃L2, T2⦄.
/2 width=4/ qed.

(* Basic forward lemmas *****************************************************)

lemma fsups_fwd_cw: ∀L1,L2,T1,T2. ⦃L1, T1⦄ ⊃* ⦃L2, T2⦄ → ♯{L2, T2} ≤ ♯{L1, T1}.
#L1 #L2 #T1 #T2 #H @(fsups_ind … H) -L2 -T2 //
/4 width=3 by fsup_fwd_cw, lt_to_le_to_lt, lt_to_le/ (**) (* slow even with trace *)
qed-.
(*
(* Advanced inversion lemmas on plus-iterated supclosure ********************)

lemma fsupp_inv_bind1_fsups: ∀b,J,L1,L2,W,U,T2. ⦃L1, ⓑ{b,J}W.U⦄ ⊃+ ⦃L2, T2⦄ →
                             ⦃L1, W⦄ ⊃* ⦃L2, T2⦄ ∨ ⦃L1.ⓑ{J}W, U⦄ ⊃* ⦃L2, T2⦄.
#b #J #L1 #L2 #W #U #T2 #H @(fsupp_ind … H) -L2 -T2
[ #L2 #T2 #H
  elim (fsup_inv_bind1 … H) -H * #H1 #H2 destruct /2 width=1/
| #L #T #L2 #T2 #_ #HT2 * /3 width=4/
]
qed-.

lemma fsupp_inv_flat1_fsups: ∀J,L1,L2,W,U,T2. ⦃L1, ⓕ{J}W.U⦄ ⊃+ ⦃L2, T2⦄ →
                             ⦃L1, W⦄ ⊃* ⦃L2, T2⦄ ∨ ⦃L1, U⦄ ⊃* ⦃L2, T2⦄.
#J #L1 #L2 #W #U #T2 #H @(fsupp_ind … H) -L2 -T2
[ #L2 #T2 #H
  elim (fsup_inv_flat1 … H) -H #H1 * #H2 destruct /2 width=1/
| #L #T #L2 #T2 #_ #HT2 * /3 width=4/
]
qed-.
*)
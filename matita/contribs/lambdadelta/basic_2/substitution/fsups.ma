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

include "basic_2/notation/relations/suptermstar_6.ma".
include "basic_2/relocation/fsupq.ma".

(* STAR-ITERATED SUPCLOSURE *************************************************)

definition fsups: tri_relation genv lenv term ≝ tri_TC … fsupq.

interpretation "star-iterated structural successor (closure)"
   'SupTermStar G1 L1 T1 G2 L2 T2 = (fsups G1 L1 T1 G2 L2 T2).

(* Basic eliminators ********************************************************)

lemma fsups_ind: ∀G1,L1,T1. ∀R:relation3 …. R G1 L1 T1 →
                 (∀G,G2,L,L2,T,T2. ⦃G1, L1, T1⦄ ⊃* ⦃G, L, T⦄ → ⦃G, L, T⦄ ⊃⸮ ⦃G2, L2, T2⦄ → R G L T → R G2 L2 T2) →
                 ∀G2,L2,T2. ⦃G1, L1, T1⦄ ⊃* ⦃G2, L2, T2⦄ → R G2 L2 T2.
#G1 #L1 #T1 #R #IH1 #IH2 #G2 #L2 #T2 #H
@(tri_TC_star_ind … IH1 IH2 G2 L2 T2 H) //
qed-.

lemma fsups_ind_dx: ∀G2,L2,T2. ∀R:relation3 …. R G2 L2 T2 →
                    (∀G1,G,L1,L,T1,T. ⦃G1, L1, T1⦄ ⊃⸮ ⦃G, L, T⦄ → ⦃G, L, T⦄ ⊃* ⦃G2, L2, T2⦄ → R G L T → R G1 L1 T1) →
                    ∀G1,L1,T1. ⦃G1, L1, T1⦄ ⊃* ⦃G2, L2, T2⦄ → R G1 L1 T1.
#G2 #L2 #T2 #R #IH1 #IH2 #G1 #L1 #T1 #H
@(tri_TC_star_ind_dx … IH1 IH2 G1 L1 T1 H) //
qed-.

(* Basic properties *********************************************************)

lemma fsups_refl: tri_reflexive … fsups.
/2 width=1/ qed.

lemma fsupq_fsups: ∀G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊃⸮ ⦃G2, L2, T2⦄ → ⦃G1, L1, T1⦄ ⊃* ⦃G2, L2, T2⦄.
/2 width=1/ qed.

lemma fsups_strap1: ∀G1,G,G2,L1,L,L2,T1,T,T2. ⦃G1, L1, T1⦄ ⊃* ⦃G, L, T⦄ → ⦃G, L, T⦄ ⊃⸮ ⦃G2, L2, T2⦄ →
                    ⦃G1, L1, T1⦄ ⊃* ⦃G2, L2, T2⦄.
/2 width=5/ qed.

lemma fsups_strap2: ∀G1,G,G2,L1,L,L2,T1,T,T2. ⦃G1, L1, T1⦄ ⊃⸮ ⦃G, L, T⦄ → ⦃G, L, T⦄ ⊃* ⦃G2, L2, T2⦄ →
                    ⦃G1, L1, T1⦄ ⊃* ⦃G2, L2, T2⦄.
/2 width=5/ qed.

(* Basic forward lemmas *****************************************************)

lemma fsups_fwd_fw: ∀G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊃* ⦃G2, L2, T2⦄ → ♯{G2, L2, T2} ≤ ♯{G1, L1, T1}.
#G1 #G2 #L1 #L2 #T1 #T2 #H @(fsups_ind … H) -L2 -T2 //
/3 width=3 by fsupq_fwd_fw, transitive_le/ (**) (* slow even with trace *)
qed-.
(*
(* Advanced inversion lemmas on plus-iterated supclosure ********************)

lamma fsupp_inv_bind1_fsups: ∀b,J,G1,G2,L1,L2,W,U,T2. ⦃G1, L1, ⓑ{b,J}W.U⦄ ⊃+ ⦃G2, L2, T2⦄ →
                             ⦃G1, L1, W⦄ ⊃* ⦃G2, L2, T2⦄ ∨ ⦃L1.ⓑ{J}W, U⦄ ⊃* ⦃G2, L2, T2⦄.
#b #J #G1 #G2 #L1 #L2 #W #U #T2 #H @(fsupp_ind … H) -G2 -L2 -T2
[ #G2 #L2 #T2 #H
  elim (fsup_inv_bind1 … H) -H * #H1 #H2 #H3 destruct /2 width=1/
| #G #G2 #L #L2 #T #T2 #_ #HT2 * /3 width=4/
]
qad-.

lamma fsupp_inv_flat1_fsups: ∀J,G1,G2,L1,L2,W,U,T2. ⦃G1, L1, ⓕ{J}W.U⦄ ⊃+ ⦃G2, L2, T2⦄ →
                             ⦃G1, L1, W⦄ ⊃* ⦃G2, L2, T2⦄ ∨ ⦃G1, L1, U⦄ ⊃* ⦃G2, L2, T2⦄.
#J #G1 #G2 #L1 #L2 #W #U #T2 #H @(fsupp_ind … H) -G2 -L2 -T2
[ #G2 #L2 #T2 #H
  elim (fsup_inv_flat1 … H) -H #H1 * #H2 destruct /2 width=1/
| #G #G2 #L #L2 #T #T2 #_ #HT2 * /3 width=4/
]
qad-.
*)

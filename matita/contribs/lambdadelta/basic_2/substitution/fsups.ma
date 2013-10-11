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
/2 width=1 by tri_inj/ qed.

lemma fsupq_fsups: ∀G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊃⸮ ⦃G2, L2, T2⦄ → ⦃G1, L1, T1⦄ ⊃* ⦃G2, L2, T2⦄.
/2 width=1 by tri_inj/ qed.

lemma fsups_strap1: ∀G1,G,G2,L1,L,L2,T1,T,T2. ⦃G1, L1, T1⦄ ⊃* ⦃G, L, T⦄ → ⦃G, L, T⦄ ⊃⸮ ⦃G2, L2, T2⦄ →
                    ⦃G1, L1, T1⦄ ⊃* ⦃G2, L2, T2⦄.
/2 width=5 by tri_step/ qed.

lemma fsups_strap2: ∀G1,G,G2,L1,L,L2,T1,T,T2. ⦃G1, L1, T1⦄ ⊃⸮ ⦃G, L, T⦄ → ⦃G, L, T⦄ ⊃* ⦃G2, L2, T2⦄ →
                    ⦃G1, L1, T1⦄ ⊃* ⦃G2, L2, T2⦄.
/2 width=5 by tri_TC_strap/ qed.

lemma fsups_ldrop: ∀G1,G2,K1,K2,T1,T2. ⦃G1, K1, T1⦄ ⊃* ⦃G2, K2, T2⦄ →
                   ∀L1,U1,e. ⇩[0, e] L1 ≡ K1 → ⇧[0, e] T1 ≡ U1 →
                   ⦃G1, L1, U1⦄ ⊃* ⦃G2, K2, T2⦄.
#G1 #G2 #K1 #K2 #T1 #T2 #H @(fsups_ind … H) -G2 -K2 -T2
/3 width=5 by fsups_strap1, fsupq_fsups, fsupq_drop/
qed-.

(* Basic forward lemmas *****************************************************)

lemma fsups_fwd_fw: ∀G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊃* ⦃G2, L2, T2⦄ → ♯{G2, L2, T2} ≤ ♯{G1, L1, T1}.
#G1 #G2 #L1 #L2 #T1 #T2 #H @(fsups_ind … H) -L2 -T2
/3 width=3 by fsupq_fwd_fw, transitive_le/
qed-.

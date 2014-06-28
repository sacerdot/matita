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

include "basic_2/notation/relations/suptermplus_6.ma".
include "basic_2/substitution/fqu.ma".

(* PLUS-ITERATED SUPCLOSURE *************************************************)

definition fqup: tri_relation genv lenv term ≝ tri_TC … fqu.

interpretation "plus-iterated structural successor (closure)"
   'SupTermPlus G1 L1 T1 G2 L2 T2 = (fqup G1 L1 T1 G2 L2 T2).

(* Basic properties *********************************************************)

lemma fqu_fqup: ∀G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐ ⦃G2, L2, T2⦄ → ⦃G1, L1, T1⦄ ⊐+ ⦃G2, L2, T2⦄.
/2 width=1 by tri_inj/ qed.

lemma fqup_strap1: ∀G1,G,G2,L1,L,L2,T1,T,T2.
                   ⦃G1, L1, T1⦄ ⊐+ ⦃G, L, T⦄ → ⦃G, L, T⦄ ⊐ ⦃G2, L2, T2⦄ →
                   ⦃G1, L1, T1⦄ ⊐+ ⦃G2, L2, T2⦄.
/2 width=5 by tri_step/ qed.

lemma fqup_strap2: ∀G1,G,G2,L1,L,L2,T1,T,T2.
                   ⦃G1, L1, T1⦄ ⊐ ⦃G, L, T⦄ → ⦃G, L, T⦄ ⊐+ ⦃G2, L2, T2⦄ →
                   ⦃G1, L1, T1⦄ ⊐+ ⦃G2, L2, T2⦄.
/2 width=5 by tri_TC_strap/ qed.

lemma fqup_drop: ∀G1,G2,L1,K1,K2,T1,T2,U1,e. ⇩[e] L1 ≡ K1 → ⇧[0, e] T1 ≡ U1 →
                  ⦃G1, K1, T1⦄ ⊐+ ⦃G2, K2, T2⦄ → ⦃G1, L1, U1⦄ ⊐+ ⦃G2, K2, T2⦄.
#G1 #G2 #L1 #K1 #K2 #T1 #T2 #U1 #e #HLK1 #HTU1 #HT12 elim (eq_or_gt … e) #H destruct
[ >(drop_inv_O2 … HLK1) -L1 <(lift_inv_O2 … HTU1) -U1 //
| /3 width=5 by fqup_strap2, fqu_drop_lt/
]
qed-.

lemma fqup_lref: ∀I,G,L,K,V,i. ⇩[i] L ≡ K.ⓑ{I}V → ⦃G, L, #i⦄ ⊐+ ⦃G, K, V⦄.
/3 width=6 by fqu_lref_O, fqu_fqup, lift_lref_ge, fqup_drop/ qed.

lemma fqup_pair_sn: ∀I,G,L,V,T. ⦃G, L, ②{I}V.T⦄ ⊐+ ⦃G, L, V⦄.
/2 width=1 by fqu_pair_sn, fqu_fqup/ qed.

lemma fqup_bind_dx: ∀a,I,G,L,V,T. ⦃G, L, ⓑ{a,I}V.T⦄ ⊐+ ⦃G, L.ⓑ{I}V, T⦄.
/2 width=1 by fqu_bind_dx, fqu_fqup/ qed.

lemma fqup_flat_dx: ∀I,G,L,V,T. ⦃G, L, ⓕ{I}V.T⦄ ⊐+ ⦃G, L, T⦄.
/2 width=1 by fqu_flat_dx, fqu_fqup/ qed.

lemma fqup_flat_dx_pair_sn: ∀I1,I2,G,L,V1,V2,T. ⦃G, L, ⓕ{I1}V1.②{I2}V2.T⦄ ⊐+ ⦃G, L, V2⦄.
/2 width=5 by fqu_pair_sn, fqup_strap1/ qed.

lemma fqup_bind_dx_flat_dx: ∀a,G,I1,I2,L,V1,V2,T. ⦃G, L, ⓑ{a,I1}V1.ⓕ{I2}V2.T⦄ ⊐+ ⦃G, L.ⓑ{I1}V1, T⦄.
/2 width=5 by fqu_flat_dx, fqup_strap1/ qed.

lemma fqup_flat_dx_bind_dx: ∀a,I1,I2,G,L,V1,V2,T. ⦃G, L, ⓕ{I1}V1.ⓑ{a,I2}V2.T⦄ ⊐+ ⦃G, L.ⓑ{I2}V2, T⦄.
/2 width=5 by fqu_bind_dx, fqup_strap1/ qed.

(* Basic eliminators ********************************************************)

lemma fqup_ind: ∀G1,L1,T1. ∀R:relation3 ….
                (∀G2,L2,T2. ⦃G1, L1, T1⦄ ⊐ ⦃G2, L2, T2⦄ → R G2 L2 T2) →
                (∀G,G2,L,L2,T,T2. ⦃G1, L1, T1⦄ ⊐+ ⦃G, L, T⦄ → ⦃G, L, T⦄ ⊐ ⦃G2, L2, T2⦄ → R G L T → R G2 L2 T2) →
                ∀G2,L2,T2. ⦃G1, L1, T1⦄ ⊐+ ⦃G2, L2, T2⦄ → R G2 L2 T2.
#G1 #L1 #T1 #R #IH1 #IH2 #G2 #L2 #T2 #H
@(tri_TC_ind … IH1 IH2 G2 L2 T2 H)
qed-.

lemma fqup_ind_dx: ∀G2,L2,T2. ∀R:relation3 ….
                   (∀G1,L1,T1. ⦃G1, L1, T1⦄ ⊐ ⦃G2, L2, T2⦄ → R G1 L1 T1) →
                   (∀G1,G,L1,L,T1,T. ⦃G1, L1, T1⦄ ⊐ ⦃G, L, T⦄ → ⦃G, L, T⦄ ⊐+ ⦃G2, L2, T2⦄ → R G L T → R G1 L1 T1) →
                   ∀G1,L1,T1. ⦃G1, L1, T1⦄ ⊐+ ⦃G2, L2, T2⦄ → R G1 L1 T1.
#G2 #L2 #T2 #R #IH1 #IH2 #G1 #L1 #T1 #H
@(tri_TC_ind_dx … IH1 IH2 G1 L1 T1 H)
qed-.

(* Basic forward lemmas *****************************************************)

lemma fqup_fwd_fw: ∀G1,G2,L1,L2,T1,T2.
                   ⦃G1, L1, T1⦄ ⊐+ ⦃G2, L2, T2⦄ → ♯{G2, L2, T2} < ♯{G1, L1, T1}.
#G1 #G2 #L1 #L2 #T1 #T2 #H @(fqup_ind … H) -G2 -L2 -T2
/3 width=3 by fqu_fwd_fw, transitive_lt/
qed-.

(* Advanced eliminators *****************************************************)

lemma fqup_wf_ind: ∀R:relation3 …. (
                      ∀G1,L1,T1. (∀G2,L2,T2. ⦃G1, L1, T1⦄ ⊐+ ⦃G2, L2, T2⦄ → R G2 L2 T2) →
                      R G1 L1 T1
                   ) → ∀G1,L1,T1. R G1 L1 T1.
#R #HR @(f3_ind … fw) #n #IHn #G1 #L1 #T1 #H destruct /4 width=1 by fqup_fwd_fw/
qed-.

lemma fqup_wf_ind_eq: ∀R:relation3 …. (
                         ∀G1,L1,T1. (∀G2,L2,T2. ⦃G1, L1, T1⦄ ⊐+ ⦃G2, L2, T2⦄ → R G2 L2 T2) →
                         ∀G2,L2,T2. G1 = G2 → L1 = L2 → T1 = T2 → R G2 L2 T2
                      ) → ∀G1,L1,T1. R G1 L1 T1.
#R #HR @(f3_ind … fw) #n #IHn #G1 #L1 #T1 #H destruct /4 width=7 by fqup_fwd_fw/
qed-.

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
include "basic_2/relocation/fsup.ma".

(* PLUS-ITERATED SUPCLOSURE *************************************************)

definition fsupp: tri_relation genv lenv term ≝ tri_TC … fsup.

interpretation "plus-iterated structural successor (closure)"
   'SupTermPlus G1 L1 T1 G2 L2 T2 = (fsupp G1 L1 T1 G2 L2 T2).

(* Basic properties *********************************************************)

lemma fsup_fsupp: ∀G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊃ ⦃G2, L2, T2⦄ → ⦃G1, L1, T1⦄ ⊃+ ⦃G2, L2, T2⦄.
/2 width=1/ qed.

lemma fsupp_strap1: ∀G1,G,G2,L1,L,L2,T1,T,T2.
                    ⦃G1, L1, T1⦄ ⊃+ ⦃G, L, T⦄ → ⦃G, L, T⦄ ⊃ ⦃G2, L2, T2⦄ →
                    ⦃G1, L1, T1⦄ ⊃+ ⦃G2, L2, T2⦄.
/2 width=5/ qed.

lemma fsupp_strap2: ∀G1,G,G2,L1,L,L2,T1,T,T2.
                    ⦃G1, L1, T1⦄ ⊃ ⦃G, L, T⦄ → ⦃G, L, T⦄ ⊃+ ⦃G2, L2, T2⦄ →
                    ⦃G1, L1, T1⦄ ⊃+ ⦃G2, L2, T2⦄.
/2 width=5/ qed.

lemma fsupp_lref: ∀I,G,L,K,V,i. ⇩[0, i] L ≡ K.ⓑ{I}V → ⦃G, L, #i⦄ ⊃+ ⦃G, K, V⦄.
/3 width=2/ qed.

lemma fsupp_pair_sn: ∀I,G,L,V,T. ⦃G, L, ②{I}V.T⦄ ⊃+ ⦃G, L, V⦄.
/2 width=1/ qed.

lemma fsupp_bind_dx: ∀a,I,G,L,V,T. ⦃G, L, ⓑ{a,I}V.T⦄ ⊃+ ⦃G, L.ⓑ{I}V, T⦄.
/2 width=1/ qed.

lemma fsupp_flat_dx: ∀I,G,L,V,T. ⦃G, L, ⓕ{I}V.T⦄ ⊃+ ⦃G, L, T⦄.
/2 width=1/ qed.

lemma fsupp_flat_dx_pair_sn: ∀I1,I2,G,L,V1,V2,T. ⦃G, L, ⓕ{I1}V1.②{I2}V2.T⦄ ⊃+ ⦃G, L, V2⦄.
/2 width=5/ qed.

lemma fsupp_bind_dx_flat_dx: ∀a,G,I1,I2,L,V1,V2,T. ⦃G, L, ⓑ{a,I1}V1.ⓕ{I2}V2.T⦄ ⊃+ ⦃G, L.ⓑ{I1}V1, T⦄.
/2 width=5/ qed.

lemma fsupp_flat_dx_bind_dx: ∀a,I1,I2,G,L,V1,V2,T. ⦃G, L, ⓕ{I1}V1.ⓑ{a,I2}V2.T⦄ ⊃+ ⦃G, L.ⓑ{I2}V2, T⦄.
/2 width=5/ qed.

(* Basic eliminators ********************************************************)

lemma fsupp_ind: ∀G1,L1,T1. ∀R:relation3 ….
                 (∀G2,L2,T2. ⦃G1, L1, T1⦄ ⊃ ⦃G2, L2, T2⦄ → R G2 L2 T2) →
                 (∀G,G2,L,L2,T,T2. ⦃G1, L1, T1⦄ ⊃+ ⦃G, L, T⦄ → ⦃G, L, T⦄ ⊃ ⦃G2, L2, T2⦄ → R G L T → R G2 L2 T2) →
                 ∀G2,L2,T2. ⦃G1, L1, T1⦄ ⊃+ ⦃G2, L2, T2⦄ → R G2 L2 T2.
#G1 #L1 #T1 #R #IH1 #IH2 #G2 #L2 #T2 #H
@(tri_TC_ind … IH1 IH2 G2 L2 T2 H)
qed-.

lemma fsupp_ind_dx: ∀G2,L2,T2. ∀R:relation3 ….
                    (∀G1,L1,T1. ⦃G1, L1, T1⦄ ⊃ ⦃G2, L2, T2⦄ → R G1 L1 T1) →
                    (∀G1,G,L1,L,T1,T. ⦃G1, L1, T1⦄ ⊃ ⦃G, L, T⦄ → ⦃G, L, T⦄ ⊃+ ⦃G2, L2, T2⦄ → R G L T → R G1 L1 T1) →
                    ∀G1,L1,T1. ⦃G1, L1, T1⦄ ⊃+ ⦃G2, L2, T2⦄ → R G1 L1 T1.
#G2 #L2 #T2 #R #IH1 #IH2 #G1 #L1 #T1 #H
@(tri_TC_ind_dx … IH1 IH2 G1 L1 T1 H)
qed-.

(* Basic forward lemmas *****************************************************)

lemma fsupp_fwd_fw: ∀G1,G2,L1,L2,T1,T2.
                    ⦃G1, L1, T1⦄ ⊃+ ⦃G2, L2, T2⦄ → ♯{G2, L2, T2} < ♯{G1, L1, T1}.
#G1 #G2 #L1 #L2 #T1 #T2 #H @(fsupp_ind … H) -G2 -L2 -T2
/3 width=3 by fsup_fwd_fw, transitive_lt/
qed-.

(* Advanced eliminators *****************************************************)

lemma fsupp_wf_ind: ∀R:relation3 …. (
                       ∀G1,L1,T1. (∀G2,L2,T2. ⦃G1, L1, T1⦄ ⊃+ ⦃G2, L2, T2⦄ → R G2 L2 T2) →
                       ∀G2,L2,T2. G1 = G2 → L1 = L2 → T1 = T2 → R G2 L2 T2
                    ) → ∀G1,L1,T1. R G1 L1 T1.
#R #HR @(f3_ind … fw) #n #IHn #G1 #L1 #T1 #H destruct /4 width=7 by fsupp_fwd_fw/
qed-.

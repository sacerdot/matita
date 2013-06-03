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

include "basic_2/relocation/fsup.ma".

(* PLUS-ITERATED SUPCLOSURE *************************************************)

definition fsupp: bi_relation lenv term ≝ bi_TC … fsup.

interpretation "plus-iterated structural successor (closure)"
   'SupTermPlus L1 T1 L2 T2 = (fsupp L1 T1 L2 T2).

(* Basic properties *********************************************************)

lemma fsup_fsupp: ∀L1,L2,T1,T2. ⦃L1, T1⦄ ⊃ ⦃L2, T2⦄ → ⦃L1, T1⦄ ⊃+ ⦃L2, T2⦄.
/2 width=1/ qed.

lemma fsupp_strap1: ∀L1,L,L2,T1,T,T2. ⦃L1, T1⦄ ⊃+ ⦃L, T⦄ → ⦃L, T⦄ ⊃ ⦃L2, T2⦄ →
                    ⦃L1, T1⦄ ⊃+ ⦃L2, T2⦄.
/2 width=4/ qed.

lemma fsupp_strap2: ∀L1,L,L2,T1,T,T2. ⦃L1, T1⦄ ⊃ ⦃L, T⦄ → ⦃L, T⦄ ⊃+ ⦃L2, T2⦄ →
                    ⦃L1, T1⦄ ⊃+ ⦃L2, T2⦄.
/2 width=4/ qed.

lemma fsupp_lref: ∀I,K,V,i,L. ⇩[0, i] L ≡ K.ⓑ{I}V → ⦃L, #i⦄ ⊃+ ⦃K, V⦄.
/3 width=2/ qed.

lemma fsupp_pair_sn: ∀I,L,V,T. ⦃L, ②{I}V.T⦄ ⊃+ ⦃L, V⦄.
/2 width=1/ qed.

lemma fsupp_bind_dx: ∀a,K,I,V,T. ⦃K, ⓑ{a,I}V.T⦄ ⊃+ ⦃K.ⓑ{I}V, T⦄.
/2 width=1/ qed.

lemma fsupp_flat_dx: ∀I,L,V,T. ⦃L, ⓕ{I}V.T⦄ ⊃+ ⦃L, T⦄.
/2 width=1/ qed.

lemma fsupp_flat_dx_pair_sn: ∀I1,I2,L,V1,V2,T. ⦃L, ⓕ{I1}V1.②{I2}V2.T⦄ ⊃+ ⦃L, V2⦄.
/2 width=4/ qed.

lemma fsupp_bind_dx_flat_dx: ∀a,I1,I2,L,V1,V2,T. ⦃L, ⓑ{a,I1}V1.ⓕ{I2}V2.T⦄ ⊃+ ⦃L.ⓑ{I1}V1, T⦄.
/2 width=4/ qed.

lemma fsupp_flat_dx_bind_dx: ∀a,I1,I2,L,V1,V2,T. ⦃L, ⓕ{I1}V1.ⓑ{a,I2}V2.T⦄ ⊃+ ⦃L.ⓑ{I2}V2, T⦄.
/2 width=4/ qed.
(*
lemma fsupp_append_sn: ∀I,L,K,V,T. ⦃L.ⓑ{I}V@@K, T⦄ ⊃+ ⦃L, V⦄.
#I #L #K #V *
[ * #i
normalize /3 width=1 by monotonic_lt_plus_l, monotonic_le_plus_r/ (**) (* auto too slow without trace *)
qed.
*)
(* Basic eliminators ********************************************************)

lemma fsupp_ind: ∀L1,T1. ∀R:relation2 lenv term.
                 (∀L2,T2. ⦃L1, T1⦄ ⊃ ⦃L2, T2⦄ → R L2 T2) →
                 (∀L,T,L2,T2. ⦃L1, T1⦄ ⊃+ ⦃L, T⦄ → ⦃L, T⦄ ⊃ ⦃L2, T2⦄ → R L T → R L2 T2) →
                 ∀L2,T2. ⦃L1, T1⦄ ⊃+ ⦃L2, T2⦄ → R L2 T2.
#L1 #T1 #R #IH1 #IH2 #L2 #T2 #H
@(bi_TC_ind … IH1 IH2 ? ? H)
qed-.

lemma fsupp_ind_dx: ∀L2,T2. ∀R:relation2 lenv term.
                    (∀L1,T1. ⦃L1, T1⦄ ⊃ ⦃L2, T2⦄ → R L1 T1) →
                    (∀L1,L,T1,T. ⦃L1, T1⦄ ⊃ ⦃L, T⦄ → ⦃L, T⦄ ⊃+ ⦃L2, T2⦄ → R L T → R L1 T1) →
                    ∀L1,T1. ⦃L1, T1⦄ ⊃+ ⦃L2, T2⦄ → R L1 T1.
#L2 #T2 #R #IH1 #IH2 #L1 #T1 #H
@(bi_TC_ind_dx … IH1 IH2 ? ? H)
qed-.

(* Basic forward lemmas *****************************************************)

lemma fsupp_fwd_fw: ∀L1,L2,T1,T2. ⦃L1, T1⦄ ⊃+ ⦃L2, T2⦄ → ♯{L2, T2} < ♯{L1, T1}.
#L1 #L2 #T1 #T2 #H @(fsupp_ind … H) -L2 -T2
/3 width=3 by fsup_fwd_fw, transitive_lt/
qed-.

(* Advanced eliminators *****************************************************)

lemma fsupp_wf_ind: ∀R:relation2 lenv term. (
                       ∀L1,T1. (∀L2,T2. ⦃L1, T1⦄ ⊃+ ⦃L2, T2⦄ → R L2 T2) →
                       ∀L2,T2. L1 = L2 → T1 = T2 → R L2 T2
                    ) → ∀L1,T1. R L1 T1.
#R #HR @(f2_ind … fw) #n #IHn #L1 #T1 #H destruct /4 width=5 by fsupp_fwd_fw/
qed-.

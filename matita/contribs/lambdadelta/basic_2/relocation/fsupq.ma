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

(* OPTIONAL SUPCLOSURE ******************************************************)

inductive fsupq: bi_relation lenv term ≝
| fsupq_refl   : ∀L,T. fsupq L T L T
| fsupq_lref_O : ∀I,L,V. fsupq (L.ⓑ{I}V) (#0) L V
| fsupq_pair_sn: ∀I,L,V,T. fsupq L (②{I}V.T) L V
| fsupq_bind_dx: ∀a,I,L,V,T. fsupq L (ⓑ{a,I}V.T) (L.ⓑ{I}V) T
| fsupq_flat_dx: ∀I,L,V,T.   fsupq L (ⓕ{I}V.T) L T
| fsupq_ldrop  : ∀L1,K1,K2,T1,T2,U1,d,e.
                ⇩[d, e] L1 ≡ K1 → ⇧[d, e] T1 ≡ U1 →
                fsupq K1 T1 K2 T2 → fsupq L1 U1 K2 T2
.

interpretation
   "optional structural successor (closure)"
   'SupTermOpt L1 T1 L2 T2 = (fsupq L1 T1 L2 T2).

(* Basic properties *********************************************************)

lemma fsup_fsupq: ∀L1,L2,T1,T2. ⦃L1, T1⦄ ⊃ ⦃L2, T2⦄ → ⦃L1, T1⦄ ⊃⸮ ⦃L2, T2⦄.
#L1 #L2 #T1 #T2 #H elim H -L1 -L2 -T1 -T2 // /2 width=7/ qed.

(* Basic properties *********************************************************)

lemma fsupq_lref_S_lt: ∀I,L,K,V,T,i. 0 < i → ⦃L, #(i-1)⦄ ⊃⸮ ⦃K, T⦄ → ⦃L.ⓑ{I}V, #i⦄ ⊃⸮ ⦃K, T⦄.
/3 width=7/ qed.

lemma fsupq_lref: ∀I,K,V,i,L. ⇩[0, i] L ≡ K.ⓑ{I}V → ⦃L, #i⦄ ⊃⸮ ⦃K, V⦄.
/3 width=2/ qed.

(* Basic forward lemmas *****************************************************)

lemma fsupq_fwd_fw: ∀L1,L2,T1,T2. ⦃L1, T1⦄ ⊃⸮ ⦃L2, T2⦄ → ♯{L2, T2} ≤ ♯{L1, T1}.
#L1 #L2 #T1 #T2 #H elim H -L1 -L2 -T1 -T2 // [1,2,3: /2 width=1/ ]
#L1 #K1 #K2 #T1 #T2 #U1 #d #e #HLK1 #HTU1 #_ #IHT12
lapply (ldrop_fwd_lw … HLK1) -HLK1 #HLK1
lapply (lift_fwd_tw … HTU1) -HTU1 #HTU1
@(transitive_le … IHT12) -IHT12 /2 width=1/
qed-.

fact fsupq_fwd_length_lref1_aux: ∀L1,L2,T1,T2. ⦃L1, T1⦄ ⊃⸮ ⦃L2, T2⦄ →
                                 ∀i. T1 = #i → |L2| ≤ |L1|.
#L1 #L2 #T1 #T2 #H elim H -L1 -L2 -T1 -T2 //
[ #a #I #L #V #T #j #H destruct
| #L1 #K1 #K2 #T1 #T2 #U1 #d #e #HLK1 #HTU1 #_ #IHT12 #i #H destruct
  lapply (ldrop_fwd_length … HLK1) -HLK1 #HLK1
  elim (lift_inv_lref2 … HTU1) -HTU1 * #Hdei #H destruct
  @(transitive_le … HLK1) /2 width=2/
]
qed-.

lemma fsupq_fwd_length_lref1: ∀L1,L2,T2,i. ⦃L1, #i⦄ ⊃⸮ ⦃L2, T2⦄ → |L2| ≤ |L1|.
/2 width=5 by fsupq_fwd_length_lref1_aux/
qed-.

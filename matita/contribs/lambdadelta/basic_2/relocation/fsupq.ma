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

include "basic_2/notation/relations/suptermopt_6.ma".
include "basic_2/relocation/fsup.ma".

(* OPTIONAL SUPCLOSURE ******************************************************)

(* activate genv *)
inductive fsupq: tri_relation genv lenv term ≝
| fsupq_refl   : ∀G,L,T. fsupq G L T G L T
| fsupq_lref_O : ∀I,G,L,V. fsupq G (L.ⓑ{I}V) (#0) G L V
| fsupq_pair_sn: ∀I,G,L,V,T. fsupq G L (②{I}V.T) G L V
| fsupq_bind_dx: ∀a,I,G,L,V,T. fsupq G L (ⓑ{a,I}V.T) G (L.ⓑ{I}V) T
| fsupq_flat_dx: ∀I,G, L,V,T. fsupq G L (ⓕ{I}V.T) G L T
| fsupq_ldrop  : ∀G1,G2,L1,K1,K2,T1,T2,U1,d,e.
                 ⇩[d, e] L1 ≡ K1 → ⇧[d, e] T1 ≡ U1 →
                 fsupq G1 K1 T1 G2 K2 T2 → fsupq G1 L1 U1 G2 K2 T2
.

interpretation
   "optional structural successor (closure)"
   'SupTermOpt G1 L1 T1 G2 L2 T2 = (fsupq G1 L1 T1 G2 L2 T2).

(* Basic properties *********************************************************)

lemma fsup_fsupq: ∀G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊃ ⦃G2, L2, T2⦄ → ⦃G1, L1, T1⦄ ⊃⸮ ⦃G2, L2, T2⦄.
#G1 #G2 #L1 #L2 #T1 #T2 #H elim H -L1 -L2 -T1 -T2 // /2 width=7/ qed.

(* Basic properties *********************************************************)

lemma fsupq_lref_S_lt: ∀I,G1,G2,L,K,V,T,i.
                       0 < i → ⦃G1, L, #(i-1)⦄ ⊃⸮ ⦃G2, K, T⦄ → ⦃G1, L.ⓑ{I}V, #i⦄ ⊃⸮ ⦃G2, K, T⦄.
/3 width=7/ qed.

lemma fsupq_lref: ∀I,G,K,V,i,L. ⇩[0, i] L ≡ K.ⓑ{I}V → ⦃G, L, #i⦄ ⊃⸮ ⦃G, K, V⦄.
/3 width=2/ qed.

(* Basic forward lemmas *****************************************************)

lemma fsupq_fwd_fw: ∀G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊃⸮ ⦃G2, L2, T2⦄ → ♯{G2, L2, T2} ≤ ♯{G1, L1, T1}.
#G1 #G2 #L1 #L2 #T1 #T2 #H elim H -G1 -G2 -L1 -L2 -T1 -T2 // [1,2,3: /2 width=1/ ]
#G1 #G2 #L1 #K1 #K2 #T1 #T2 #U1 #d #e #HLK1 #HTU1 #_ #IHT12
lapply (ldrop_fwd_lw … HLK1) -HLK1 #HLK1
lapply (lift_fwd_tw … HTU1) -HTU1 #HTU1
@(transitive_le … IHT12) -IHT12 /2 width=1/
qed-.

fact fsupq_fwd_length_lref1_aux: ∀G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊃⸮ ⦃G2, L2, T2⦄ →
                                 ∀i. T1 = #i → |L2| ≤ |L1|.
#G1 #G2 #L1 #L2 #T1 #T2 #H elim H -G1 -G2 -L1 -L2 -T1 -T2 //
[ #a #I #G #L #V #T #j #H destruct
| #G1 #G2 #L1 #K1 #K2 #T1 #T2 #U1 #d #e #HLK1 #HTU1 #_ #IHT12 #i #H destruct
  lapply (ldrop_fwd_length_le4 … HLK1) -HLK1 #HLK1
  elim (lift_inv_lref2 … HTU1) -HTU1 * #Hdei #H destruct
  @(transitive_le … HLK1) /2 width=2/
]
qed-.

lemma fsupq_fwd_length_lref1: ∀G1,G2,L1,L2,T2,i. ⦃G1, L1, #i⦄ ⊃⸮ ⦃G2, L2, T2⦄ → |L2| ≤ |L1|.
/2 width=7 by fsupq_fwd_length_lref1_aux/
qed-.

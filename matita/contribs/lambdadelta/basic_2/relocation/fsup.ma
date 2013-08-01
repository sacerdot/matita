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

include "basic_2/notation/relations/supterm_6.ma".
include "basic_2/grammar/cl_weight.ma".
include "basic_2/relocation/ldrop.ma".

(* SUPCLOSURE ***************************************************************)

(* activate genv *)
inductive fsup: tri_relation genv lenv term ≝
| fsup_lref_O  : ∀I,G,L,V. fsup G (L.ⓑ{I}V) (#0) G L V
| fsup_pair_sn : ∀I,G,L,V,T. fsup G L (②{I}V.T) G L V
| fsup_bind_dx : ∀a,I,G,L,V,T. fsup G L (ⓑ{a,I}V.T) G (L.ⓑ{I}V) T
| fsup_flat_dx : ∀I,G,L,V,T. fsup G L (ⓕ{I}V.T) G L T
| fsup_ldrop_lt: ∀G,L,K,T,U,d,e.
                 ⇩[d, e] L ≡ K → ⇧[d, e] T ≡ U → 0 < e → fsup G L U G K T
| fsup_ldrop   : ∀G1,G2,L1,K1,K2,T1,T2,U1,d,e.
                 ⇩[d, e] L1 ≡ K1 → ⇧[d, e] T1 ≡ U1 →
                 fsup G1 K1 T1 G2 K2 T2 → fsup G1 L1 U1 G2 K2 T2
.

interpretation
   "structural successor (closure)"
   'SupTerm G1 L1 T1 G2 L2 T2 = (fsup G1 L1 T1 G2 L2 T2).

(* Basic properties *********************************************************)

lemma fsup_lref_S_lt: ∀I,G1,G2,L,K,V,T,i. 0 < i → ⦃G1, L, #(i-1)⦄ ⊃ ⦃G2, K, T⦄ → ⦃G1, L.ⓑ{I}V, #i⦄ ⊃ ⦃G2, K, T⦄.
#I #G1 #G2 #L #K #V #T #i #Hi #H /3 width=7 by fsup_ldrop, ldrop_ldrop, lift_lref_ge_minus/ (**) (* auto too slow without trace *)
qed.

lemma fsup_lref: ∀I,G,K,V,i,L. ⇩[0, i] L ≡ K.ⓑ{I}V → ⦃G, L, #i⦄ ⊃ ⦃G, K, V⦄.
#I #G #K #V #i @(nat_elim1 i) -i #i #IH #L #H
elim (ldrop_inv_O1_pair2 … H) -H *
[ #H1 #H2 destruct //
| #I1 #K1 #V1 #HK1 #H #Hi destruct
  lapply (IH … HK1) /2 width=1/
]
qed.

(* Basic forward lemmas *****************************************************)

lemma fsup_fwd_fw: ∀G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊃ ⦃G2, L2, T2⦄ → ♯{G2, L2, T2} < ♯{G1, L1, T1}.
#G1 #G2 #L1 #L2 #T1 #T2 #H elim H -G1 -G2 -L1 -L2 -T1 -T2 //
[ #G #L #K #T #U #d #e #HLK #HTU #HKL
  lapply (ldrop_fwd_lw_lt … HLK HKL) -HKL -HLK #HKL
  lapply (lift_fwd_tw … HTU) -d -e #H
  normalize in ⊢ (?%%); /2 width=1/
| #G1 #G2 #L1 #K1 #K2 #T1 #T2 #U1 #d #e #HLK1 #HTU1 #_ #IHT12
  lapply (ldrop_fwd_lw … HLK1) -HLK1 #HLK1
  lapply (lift_fwd_tw … HTU1) -HTU1 #HTU1
  @(lt_to_le_to_lt … IHT12) -IHT12 /2 width=1/
]
qed-.

fact fsup_fwd_length_lref1_aux: ∀G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊃ ⦃G2, L2, T2⦄ →
                                ∀i. T1 = #i → |L2| < |L1|.
#G1 #G2 #L1 #L2 #T1 #T2 #H elim H -G1 -G2 -L1 -L2 -T1 -T2
[1: normalize //
|3: #a
|5: /2 width=4 by ldrop_fwd_length_lt4/
|6: #G1 #G2 #L1 #K1 #K2 #T1 #T2 #U1 #d #e #HLK1 #HTU1 #_ #IHT12 #i #H destruct
    lapply (ldrop_fwd_length_le4 … HLK1) -HLK1 #HLK1
    elim (lift_inv_lref2 … HTU1) -HTU1 * #Hdei #H destruct
    @(lt_to_le_to_lt … HLK1) /2 width=2/
] #I #G #L #V #T #j #H destruct
qed-.

lemma fsup_fwd_length_lref1: ∀G1,G2,L1,L2,T2,i. ⦃G1, L1, #i⦄ ⊃ ⦃G2, L2, T2⦄ → |L2| < |L1|.
/2 width=7 by fsup_fwd_length_lref1_aux/
qed-.

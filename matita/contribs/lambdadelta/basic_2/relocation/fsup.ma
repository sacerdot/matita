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

include "basic_2/relocation/ldrop.ma".

(* SUPCLOSURE ***************************************************************)

inductive fsup: bi_relation lenv term ≝
| fsup_lref   : ∀I,L,V. fsup (L.ⓑ{I}V) (#0) L V
| fsup_pair_sn: ∀I,L,V,T. fsup L (②{I}V.T) L V
| fsup_bind_dx: ∀a,I,L,V,T. fsup L (ⓑ{a,I}V.T) (L.ⓑ{I}V) T
| fsup_flat_dx: ∀I,L,V,T.   fsup L (ⓕ{I}V.T) L T
| fsup_ldrop  : ∀L1,K1,K2,T1,T2,U1,d,e.
                ⇩[d, e] L1 ≡ K1 → ⇧[d, e] T1 ≡ U1 →
                fsup K1 T1 K2 T2 → fsup L1 U1 K2 T2
.

interpretation
   "structural successor (closure)"
   'SupTerm L1 T1 L2 T2 = (fsup L1 T1 L2 T2).

(* Basic properties *********************************************************)

lemma fsup_lref_S_lt: ∀I,L,K,V,T,i. 0 < i → ⦃L, #(i-1)⦄ ⊃ ⦃K, T⦄ → ⦃L.ⓑ{I}V, #i⦄ ⊃ ⦃K, T⦄.
/3 width=7/ qed.

lemma fsup_lref: ∀I,K,V,i,L. ⇩[0, i] L ≡ K.ⓑ{I}V → ⦃L, #i⦄ ⊃ ⦃K, V⦄.
#I #K #V #i @(nat_elim1 i) -i #i #IH #L #H
elim (ldrop_inv_O1_pair2 … H) -H *
[ #H1 #H2 destruct //
| #I1 #K1 #V1 #HK1 #H #Hi destruct
  lapply (IH … HK1) /2 width=1/
]
qed.

(* Basic forward lemmas *****************************************************)

lemma fsup_fwd_cw: ∀L1,L2,T1,T2. ⦃L1, T1⦄ ⊃ ⦃L2, T2⦄ → ♯{L2, T2} < ♯{L1, T1}.
#L1 #L2 #T1 #T2 #H elim H -L1 -L2 -T1 -T2 //
#L1 #K1 #K2 #T1 #T2 #U1 #d #e #HLK1 #HTU1 #_ #IHT12
lapply (ldrop_fwd_lw … HLK1) -HLK1 #HLK1
lapply (lift_fwd_tw … HTU1) -HTU1 #HTU1
@(lt_to_le_to_lt … IHT12) -IHT12 /2 width=1/
qed-.

fact fsup_fwd_length_lref1_aux: ∀L1,L2,T1,T2. ⦃L1, T1⦄ ⊃ ⦃L2, T2⦄ → ∀i. T1 = #i → |L2| < |L1|.
#L1 #L2 #T1 #T2 #H elim H -L1 -L2 -T1 -T2
[5: #L1 #K1 #K2 #T1 #T2 #U1 #d #e #HLK1 #HTU1 #_ #IHT12 #i #H destruct
    lapply (ldrop_fwd_length … HLK1) -HLK1 #HLK1
    elim (lift_inv_lref2 … HTU1) -HTU1 * #Hdei #H destruct
    @(lt_to_le_to_lt … HLK1) /2 width=2/
| normalize // |3: #a
] #I #L #V #T #j #H destruct
qed-.

lemma fsup_fwd_length_lref1: ∀L1,L2,T2,i. ⦃L1, #i⦄ ⊃ ⦃L2, T2⦄ → |L2| < |L1|.
/2 width=5 by fsup_fwd_length_lref1_aux/
qed-.

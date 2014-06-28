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
include "basic_2/substitution/drop.ma".

(* SUPCLOSURE ***************************************************************)

(* activate genv *)
inductive fqu: tri_relation genv lenv term ≝
| fqu_lref_O : ∀I,G,L,V. fqu G (L.ⓑ{I}V) (#0) G L V
| fqu_pair_sn: ∀I,G,L,V,T. fqu G L (②{I}V.T) G L V
| fqu_bind_dx: ∀a,I,G,L,V,T. fqu G L (ⓑ{a,I}V.T) G (L.ⓑ{I}V) T
| fqu_flat_dx: ∀I,G,L,V,T. fqu G L (ⓕ{I}V.T) G L T
| fqu_drop   : ∀G,L,K,T,U,e.
               ⇩[e+1] L ≡ K → ⇧[0, e+1] T ≡ U → fqu G L U G K T
.

interpretation
   "structural successor (closure)"
   'SupTerm G1 L1 T1 G2 L2 T2 = (fqu G1 L1 T1 G2 L2 T2).

(* Basic properties *********************************************************)

lemma fqu_drop_lt: ∀G,L,K,T,U,e. 0 < e →
                   ⇩[e] L ≡ K → ⇧[0, e] T ≡ U → ⦃G, L, U⦄ ⊐ ⦃G, K, T⦄.
#G #L #K #T #U #e #He >(plus_minus_m_m e 1) /2 width=3 by fqu_drop/
qed.

lemma fqu_lref_S_lt: ∀I,G,L,V,i. 0 < i → ⦃G, L.ⓑ{I}V, #i⦄ ⊐ ⦃G, L, #(i-1)⦄.
/3 width=3 by fqu_drop, drop_drop, lift_lref_ge_minus/
qed.

(* Basic forward lemmas *****************************************************)

lemma fqu_fwd_fw: ∀G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐ ⦃G2, L2, T2⦄ → ♯{G2, L2, T2} < ♯{G1, L1, T1}.
#G1 #G2 #L1 #L2 #T1 #T2 #H elim H -G1 -G2 -L1 -L2 -T1 -T2 //
#G #L #K #T #U #e #HLK #HTU
lapply (drop_fwd_lw_lt … HLK ?) -HLK // #HKL
lapply (lift_fwd_tw … HTU) -e #H
normalize in ⊢ (?%%); /2 width=1 by lt_minus_to_plus/
qed-.

fact fqu_fwd_length_lref1_aux: ∀G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐ ⦃G2, L2, T2⦄ →
                               ∀i. T1 = #i → |L2| < |L1|.
#G1 #G2 #L1 #L2 #T1 #T2 #H elim H -G1 -G2 -L1 -L2 -T1 -T2
[1: normalize //
|3: #a
|5: /2 width=4 by drop_fwd_length_lt4/
] #I #G #L #V #T #j #H destruct
qed-.

lemma fqu_fwd_length_lref1: ∀G1,G2,L1,L2,T2,i. ⦃G1, L1, #i⦄ ⊐ ⦃G2, L2, T2⦄ → |L2| < |L1|.
/2 width=7 by fqu_fwd_length_lref1_aux/
qed-.

(* Advanced eliminators *****************************************************)

lemma fqu_wf_ind: ∀R:relation3 …. (
                     ∀G1,L1,T1. (∀G2,L2,T2. ⦃G1, L1, T1⦄ ⊐ ⦃G2, L2, T2⦄ → R G2 L2 T2) →
		                R G1 L1 T1
		  ) → ∀G1,L1,T1. R G1 L1 T1.
#R #HR @(f3_ind … fw) #n #IHn #G1 #L1 #T1 #H destruct /4 width=1 by fqu_fwd_fw/
qed-.

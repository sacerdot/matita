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
| fsup_lref_O : ∀I,G,L,V. fsup G (L.ⓑ{I}V) (#0) G L V
| fsup_pair_sn: ∀I,G,L,V,T. fsup G L (②{I}V.T) G L V
| fsup_bind_dx: ∀a,I,G,L,V,T. fsup G L (ⓑ{a,I}V.T) G (L.ⓑ{I}V) T
| fsup_flat_dx: ∀I,G,L,V,T. fsup G L (ⓕ{I}V.T) G L T
| fsup_drop   : ∀G,L,K,T,U,e.
                ⇩[0, e+1] L ≡ K → ⇧[0, e+1] T ≡ U → fsup G L U G K T
.

interpretation
   "structural successor (closure)"
   'SupTerm G1 L1 T1 G2 L2 T2 = (fsup G1 L1 T1 G2 L2 T2).

(* Basic properties *********************************************************)

lemma fsup_drop_lt: ∀G,L,K,T,U,e. 0 < e →
                    ⇩[0, e] L ≡ K → ⇧[0, e] T ≡ U → fsup G L U G K T.
#G #L #K #T #U #e #He >(plus_minus_m_m e 1) /2 width=3 by fsup_drop/
qed.

lemma fsup_lref_S_lt: ∀I,G,L,V,i. 0 < i → ⦃G, L.ⓑ{I}V, #i⦄ ⊃ ⦃G, L, #(i-1)⦄.
/3 width=3 by fsup_drop, ldrop_ldrop, lift_lref_ge_minus/
qed.

(* Basic forward lemmas *****************************************************)

lemma fsup_fwd_fw: ∀G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊃ ⦃G2, L2, T2⦄ → ♯{G2, L2, T2} < ♯{G1, L1, T1}.
#G1 #G2 #L1 #L2 #T1 #T2 #H elim H -G1 -G2 -L1 -L2 -T1 -T2 //
#G #L #K #T #U #e #HLK #HTU
lapply (ldrop_fwd_lw_lt … HLK ?) -HLK // #HKL
lapply (lift_fwd_tw … HTU) -e #H
normalize in ⊢ (?%%); /2 width=1 by lt_minus_to_plus/
qed-.

fact fsup_fwd_length_lref1_aux: ∀G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊃ ⦃G2, L2, T2⦄ →
                                ∀i. T1 = #i → |L2| < |L1|.
#G1 #G2 #L1 #L2 #T1 #T2 #H elim H -G1 -G2 -L1 -L2 -T1 -T2
[1: normalize //
|3: #a
|5: /2 width=4 by ldrop_fwd_length_lt4/
] #I #G #L #V #T #j #H destruct
qed-.

lemma fsup_fwd_length_lref1: ∀G1,G2,L1,L2,T2,i. ⦃G1, L1, #i⦄ ⊃ ⦃G2, L2, T2⦄ → |L2| < |L1|.
/2 width=7 by fsup_fwd_length_lref1_aux/
qed-.

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
| fsupq_lref_O : ∀I,G,L,V. fsupq G (L.ⓑ{I}V) (#0) G L V
| fsupq_pair_sn: ∀I,G,L,V,T. fsupq G L (②{I}V.T) G L V
| fsupq_bind_dx: ∀a,I,G,L,V,T. fsupq G L (ⓑ{a,I}V.T) G (L.ⓑ{I}V) T
| fsupq_flat_dx: ∀I,G, L,V,T. fsupq G L (ⓕ{I}V.T) G L T
| fsupq_drop   : ∀G,L,K,T,U,e.
                 ⇩[0, e] L ≡ K → ⇧[0, e] T ≡ U → fsupq G L U G K T
.

interpretation
   "optional structural successor (closure)"
   'SupTermOpt G1 L1 T1 G2 L2 T2 = (fsupq G1 L1 T1 G2 L2 T2).

(* Basic properties *********************************************************)

lemma fsupq_refl: tri_reflexive … fsupq.
/2 width=3 by fsupq_drop/ qed.

lemma fsup_fsupq: ∀G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊃ ⦃G2, L2, T2⦄ → ⦃G1, L1, T1⦄ ⊃⸮ ⦃G2, L2, T2⦄.
#G1 #G2 #L1 #L2 #T1 #T2 #H elim H -L1 -L2 -T1 -T2 // /2 width=3 by fsupq_drop/
qed.

(* Basic forward lemmas *****************************************************)

lemma fsupq_fwd_fw: ∀G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊃⸮ ⦃G2, L2, T2⦄ → ♯{G2, L2, T2} ≤ ♯{G1, L1, T1}.
#G1 #G2 #L1 #L2 #T1 #T2 #H elim H -G1 -G2 -L1 -L2 -T1 -T2 /2 width=1 by lt_to_le/
#G1 #L1 #K1 #T1 #U1 #e #HLK1 #HTU1
lapply (ldrop_fwd_lw … HLK1) -HLK1
lapply (lift_fwd_tw … HTU1) -HTU1
/2 width=1 by le_plus, le_n/
qed-.

fact fsupq_fwd_length_lref1_aux: ∀G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊃⸮ ⦃G2, L2, T2⦄ →
                                 ∀i. T1 = #i → |L2| ≤ |L1|.
#G1 #G2 #L1 #L2 #T1 #T2 #H elim H -G1 -G2 -L1 -L2 -T1 -T2 //
[ #a #I #G #L #V #T #j #H destruct
| #G1 #L1 #K1 #T1 #U1 #e #HLK1 #HTU1 #i #H destruct
  /2 width=3 by ldrop_fwd_length_le4/
]
qed-.

lemma fsupq_fwd_length_lref1: ∀G1,G2,L1,L2,T2,i. ⦃G1, L1, #i⦄ ⊃⸮ ⦃G2, L2, T2⦄ → |L2| ≤ |L1|.
/2 width=7 by fsupq_fwd_length_lref1_aux/
qed-.

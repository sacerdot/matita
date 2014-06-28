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
include "basic_2/substitution/fqu.ma".

(* OPTIONAL SUPCLOSURE ******************************************************)

(* activate genv *)
inductive fquq: tri_relation genv lenv term ≝
| fquq_lref_O : ∀I,G,L,V. fquq G (L.ⓑ{I}V) (#0) G L V
| fquq_pair_sn: ∀I,G,L,V,T. fquq G L (②{I}V.T) G L V
| fquq_bind_dx: ∀a,I,G,L,V,T. fquq G L (ⓑ{a,I}V.T) G (L.ⓑ{I}V) T
| fquq_flat_dx: ∀I,G, L,V,T. fquq G L (ⓕ{I}V.T) G L T
| fquq_drop   : ∀G,L,K,T,U,e.
                ⇩[e] L ≡ K → ⇧[0, e] T ≡ U → fquq G L U G K T
.

interpretation
   "optional structural successor (closure)"
   'SupTermOpt G1 L1 T1 G2 L2 T2 = (fquq G1 L1 T1 G2 L2 T2).

(* Basic properties *********************************************************)

lemma fquq_refl: tri_reflexive … fquq.
/2 width=3 by fquq_drop/ qed.

lemma fqu_fquq: ∀G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐ ⦃G2, L2, T2⦄ → ⦃G1, L1, T1⦄ ⊐⸮ ⦃G2, L2, T2⦄.
#G1 #G2 #L1 #L2 #T1 #T2 #H elim H -L1 -L2 -T1 -T2 /2 width=3 by fquq_drop/
qed.

(* Basic forward lemmas *****************************************************)

lemma fquq_fwd_fw: ∀G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐⸮ ⦃G2, L2, T2⦄ → ♯{G2, L2, T2} ≤ ♯{G1, L1, T1}.
#G1 #G2 #L1 #L2 #T1 #T2 #H elim H -G1 -G2 -L1 -L2 -T1 -T2 /2 width=1 by lt_to_le/
#G1 #L1 #K1 #T1 #U1 #e #HLK1 #HTU1
lapply (drop_fwd_lw … HLK1) -HLK1
lapply (lift_fwd_tw … HTU1) -HTU1
/2 width=1 by le_plus, le_n/
qed-.

fact fquq_fwd_length_lref1_aux: ∀G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐⸮ ⦃G2, L2, T2⦄ →
                                ∀i. T1 = #i → |L2| ≤ |L1|.
#G1 #G2 #L1 #L2 #T1 #T2 #H elim H -G1 -G2 -L1 -L2 -T1 -T2 //
[ #a #I #G #L #V #T #j #H destruct
| #G1 #L1 #K1 #T1 #U1 #e #HLK1 #HTU1 #i #H destruct
  /2 width=3 by drop_fwd_length_le4/
]
qed-.

lemma fquq_fwd_length_lref1: ∀G1,G2,L1,L2,T2,i. ⦃G1, L1, #i⦄ ⊐⸮ ⦃G2, L2, T2⦄ → |L2| ≤ |L1|.
/2 width=7 by fquq_fwd_length_lref1_aux/
qed-.

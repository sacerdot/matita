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

include "basic_2/notation/relations/suptermoptalt_6.ma".
include "basic_2/substitution/fquq.ma".

(* OPTIONAL SUPCLOSURE ******************************************************)

(* alternative definition of fquq *)
definition fquqa: tri_relation genv lenv term ≝ tri_RC … fqu.

interpretation
   "optional structural successor (closure) alternative"
   'SupTermOptAlt G1 L1 T1 G2 L2 T2 = (fquqa G1 L1 T1 G2 L2 T2).

(* Basic properties *********************************************************)

lemma fquqa_refl: tri_reflexive … fquqa.
// qed.

lemma fquqa_drop: ∀G,L,K,T,U,e.
                  ⇩[e] L ≡ K → ⇧[0, e] T ≡ U → ⦃G, L, U⦄ ⊐⊐⸮ ⦃G, K, T⦄.
#G #L #K #T #U #e #HLK #HTU elim (eq_or_gt e)
/3 width=5 by fqu_drop_lt, or_introl/ #H destruct
>(drop_inv_O2 … HLK) -L >(lift_inv_O2 … HTU) -T //
qed.

(* Main properties **********************************************************)

theorem fquq_fquqa: ∀G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐⸮ ⦃G2, L2, T2⦄ → ⦃G1, L1, T1⦄ ⊐⊐⸮ ⦃G2, L2, T2⦄.
#G1 #G2 #L1 #L2 #T1 #T2 #H elim H -G1 -G2 -L1 -L2 -T1 -T2
/2 width=3 by fquqa_drop, fqu_lref_O, fqu_pair_sn, fqu_bind_dx, fqu_flat_dx, or_introl/
qed.

(* Main inversion properties ************************************************)

theorem fquqa_inv_fquq: ∀G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐⊐⸮ ⦃G2, L2, T2⦄ → ⦃G1, L1, T1⦄ ⊐⸮ ⦃G2, L2, T2⦄.
#G1 #G2 #L1 #L2 #T1 #T2 #H elim H -H /2 width=1 by fqu_fquq/
* #H1 #H2 #H3 destruct //
qed-.

(* Advanced inversion lemmas ************************************************)

lemma fquq_inv_gen: ∀G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐⸮ ⦃G2, L2, T2⦄ →
                    ⦃G1, L1, T1⦄ ⊐ ⦃G2, L2, T2⦄ ∨ (∧∧ G1 = G2 & L1 = L2 & T1 = T2).
#G1 #G2 #L1 #L2 #T1 #T2 #H elim (fquq_fquqa … H) -H [| * ]
/2 width=1 by or_introl/
qed-.

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
include "basic_2/relocation/fsupq.ma".

(* OPTIONAL SUPCLOSURE ******************************************************)

(* alternative definition of fsupq *)
definition fsupqa: tri_relation genv lenv term ≝ tri_RC … fsup.

interpretation
   "optional structural successor (closure) alternative"
   'SupTermOptAlt G1 L1 T1 G2 L2 T2 = (fsupqa G1 L1 T1 G2 L2 T2).

(* Basic properties *********************************************************)

lemma fsupqa_refl: tri_reflexive … fsupqa.
// qed.

lemma fsupqa_drop: ∀G,L,K,T,U,e.
                   ⇩[0, e] L ≡ K → ⇧[0, e] T ≡ U → ⦃G, L, U⦄ ⊃⊃⸮ ⦃G, K, T⦄.
#G #L #K #T #U #e #HLK #HTU elim (eq_or_gt e)
/3 width=5 by fsup_drop_lt, or_introl/ #H destruct
>(ldrop_inv_O2 … HLK) -L >(lift_inv_O2 … HTU) -T //
qed.

(* Main properties **********************************************************)

theorem fsupq_fsupqa: ∀G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊃⸮ ⦃G2, L2, T2⦄ → ⦃G1, L1, T1⦄ ⊃⊃⸮ ⦃G2, L2, T2⦄.
#G1 #G2 #L1 #L2 #T1 #T2 #H elim H -G1 -G2 -L1 -L2 -T1 -T2
/2 width=3 by fsupqa_drop, fsup_lref_O, fsup_pair_sn, fsup_bind_dx, fsup_flat_dx, or_introl/
qed.

(* Main inversion properties ************************************************)

theorem fsupqa_inv_fsupq: ∀G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊃⊃⸮ ⦃G2, L2, T2⦄ → ⦃G1, L1, T1⦄ ⊃⸮ ⦃G2, L2, T2⦄.
#G1 #G2 #L1 #L2 #T1 #T2 #H elim H -H /2 width=1 by fsup_fsupq/
* #H1 #H2 #H3 destruct //
qed-.

(* Advanced inversion lemmas ************************************************)

lemma fsupq_inv_gen: ∀G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊃⸮ ⦃G2, L2, T2⦄ →
⦃G1, L1, T1⦄ ⊃ ⦃G2, L2, T2⦄ ∨ (∧∧ G1 = G2 & L1 = L2 & T1 = T2).
#G1 #G2 #L1 #L2 #T1 #T2 #H elim (fsupq_fsupqa … H) -H [| * ]
/2 width=1 by or_introl/
qed-.

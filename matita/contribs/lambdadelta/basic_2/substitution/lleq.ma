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

include "basic_2/notation/relations/lazyeq_4.ma".
include "basic_2/substitution/cpys.ma".

(* LAZY EQUIVALENCE FOR LOCAL ENVIRONMENTS **********************************)

definition lleq: relation4 ynat term lenv lenv ≝
                 λd,T,L1,L2. |L1| = |L2| ∧
                             (∀U. ⦃⋆, L1⦄ ⊢ T ▶*[d, ∞] U ↔ ⦃⋆, L2⦄ ⊢ T ▶*[d, ∞] U).

interpretation
   "lazy equivalence (local environment)"
   'LazyEq T d L1 L2 = (lleq d T L1 L2).

(* Basic properties *********************************************************)

lemma lleq_refl: ∀d,T. reflexive … (lleq d T).
/3 width=1 by conj/ qed.

lemma lleq_sym: ∀d,T. symmetric … (lleq d T).
#d #T #L1 #L2 * /3 width=1 by iff_sym, conj/
qed-.

lemma lleq_sort: ∀L1,L2,d,k. |L1| = |L2| → L1 ⋕[⋆k, d] L2.
#L1 #L2 #d #k #HL12 @conj // -HL12
#U @conj #H >(cpys_inv_sort1 … H) -H //
qed.

lemma lleq_gref: ∀L1,L2,d,p. |L1| = |L2| → L1 ⋕[§p, d] L2.
#L1 #L2 #d #k #HL12 @conj // -HL12
#U @conj #H >(cpys_inv_gref1 … H) -H //
qed.

lemma lleq_bind: ∀a,I,L1,L2,V,T,d.
                 L1 ⋕[V, d] L2 → L1.ⓑ{I}V ⋕[T, ⫯d] L2.ⓑ{I}V →
                 L1 ⋕[ⓑ{a,I}V.T, d] L2.
#a #I #L1 #L2 #V #T #d * #HL12 #IHV * #_ #IHT @conj // -HL12
#X @conj #H elim (cpys_inv_bind1 … H) -H
#W #U #HVW #HTU #H destruct
elim (IHV W) -IHV elim (IHT U) -IHT /3 width=1 by cpys_bind/
qed.

lemma lleq_flat: ∀I,L1,L2,V,T,d.
                 L1 ⋕[V, d] L2 → L1 ⋕[T, d] L2 → L1 ⋕[ⓕ{I}V.T, d] L2.
#I #L1 #L2 #V #T #d * #HL12 #IHV * #_ #IHT @conj // -HL12
#X @conj #H elim (cpys_inv_flat1 … H) -H
#W #U #HVW #HTU #H destruct
elim (IHV W) -IHV elim (IHT U) -IHT
/3 width=1 by cpys_flat/
qed.

lemma lleq_be: ∀L1,L2,U,dt. L1 ⋕[U, dt] L2 → ∀T,d,e. ⇧[d, e] T ≡ U →
               d ≤ dt → dt ≤ d + e → L1 ⋕[U, d] L2.
#L1 #L2 #U #dt * #HL12 #IH #T #d #e #HTU #Hddt #Hdtde @conj // -HL12
#U0 elim (IH U0) -IH #H12 #H21 @conj
#HU0 elim (cpys_fwd_up … HU0 … HTU) // -HU0 /4 width=5 by cpys_weak/
qed-.

lemma lsuby_lleq_trans: ∀L2,L,T,d. L2 ⋕[T, d] L →
                        ∀L1. L1 ⊑×[d, ∞] L2 → |L1| = |L2| → L1 ⋕[T, d] L.
#L2 #L #T #d * #HL2 #IH #L1 #HL12 #H @conj // -HL2
#U elim (IH U) -IH #Hdx #Hsn @conj #HTU
[ @Hdx -Hdx -Hsn @(lsuby_cpys_trans … HTU) -HTU
  /2 width=1 by lsuby_sym/ (**) (* full auto does not work *)
| -H -Hdx /3 width=3 by lsuby_cpys_trans/
]
qed-.

lemma lleq_lsuby_trans: ∀L,L1,T,d. L ⋕[T, d] L1 →
                        ∀L2. L1 ⊑×[d, ∞] L2 → |L1| = |L2| → L ⋕[T, d] L2.
/5 width=4 by lsuby_lleq_trans, lleq_sym, lsuby_sym/ qed-.

lemma lleq_lsuby_repl: ∀L1,L2,T,d. L1 ⋕[T, d] L2 →
                       ∀K1. K1 ⊑×[d, ∞] L1 → |K1| = |L1| →
                       ∀K2. L2 ⊑×[d, ∞] K2 → |L2| = |K2| →
                       K1 ⋕[T, d] K2.
/3 width=4 by lleq_lsuby_trans, lsuby_lleq_trans/ qed-.

(* Basic forward lemmas *****************************************************)

lemma lleq_fwd_length: ∀L1,L2,T,d. L1 ⋕[T, d] L2 → |L1| = |L2|.
#L1 #L2 #T #d * //
qed-.

lemma lleq_fwd_ldrop_sn: ∀L1,L2,T,d. L1 ⋕[d, T] L2 → ∀K1,i. ⇩[i] L1 ≡ K1 →
                         ∃K2. ⇩[i] L2 ≡ K2.
#L1 #L2 #T #d #H #K1 #i #HLK1 lapply (lleq_fwd_length … H) -H
#HL12 lapply (ldrop_fwd_length_le2 … HLK1) -HLK1 /2 width=1 by ldrop_O1_le/
qed-.

lemma lleq_fwd_ldrop_dx: ∀L1,L2,T,d. L1 ⋕[d, T] L2 → ∀K2,i. ⇩[i] L2 ≡ K2 →
                         ∃K1. ⇩[i] L1 ≡ K1.
/3 width=6 by lleq_fwd_ldrop_sn, lleq_sym/ qed-.

lemma lleq_fwd_bind_sn: ∀a,I,L1,L2,V,T,d.
                        L1 ⋕[ⓑ{a,I}V.T, d] L2 → L1 ⋕[V, d] L2.
#a #I #L1 #L2 #V #T #d * #HL12 #H @conj // -HL12
#U elim (H (ⓑ{a,I}U.T)) -H
#H1 #H2 @conj
#H [ lapply (H1 ?) | lapply (H2 ?) ] -H1 -H2
/2 width=1 by cpys_bind/ -H
#H elim (cpys_inv_bind1 … H) -H
#X #Y #H1 #H2 #H destruct //
qed-.

lemma lleq_fwd_bind_dx: ∀a,I,L1,L2,V,T,d.
                        L1 ⋕[ⓑ{a,I}V.T, d] L2 → L1.ⓑ{I}V ⋕[T, ⫯d] L2.ⓑ{I}V.
#a #I #L1 #L2 #V #T #d * #HL12 #H @conj [ normalize // ] -HL12
#U elim (H (ⓑ{a,I}V.U)) -H
#H1 #H2 @conj
#H [ lapply (H1 ?) | lapply (H2 ?) ] -H1 -H2
/2 width=1 by cpys_bind/ -H
#H elim (cpys_inv_bind1 … H) -H
#X #Y #H1 #H2 #H destruct //
qed-.

lemma lleq_fwd_flat_sn: ∀I,L1,L2,V,T,d.
                        L1 ⋕[ⓕ{I}V.T, d] L2 → L1 ⋕[V, d] L2.
#I #L1 #L2 #V #T #d * #HL12 #H @conj // -HL12
#U elim (H (ⓕ{I}U.T)) -H
#H1 #H2 @conj
#H [ lapply (H1 ?) | lapply (H2 ?) ] -H1 -H2
/2 width=1 by cpys_flat/ -H
#H elim (cpys_inv_flat1 … H) -H
#X #Y #H1 #H2 #H destruct //
qed-.

lemma lleq_fwd_flat_dx: ∀I,L1,L2,V,T,d.
                        L1 ⋕[ⓕ{I}V.T, d] L2 → L1 ⋕[T, d] L2.
#I #L1 #L2 #V #T #d * #HL12 #H @conj // -HL12
#U elim (H (ⓕ{I}V.U)) -H
#H1 #H2 @conj
#H [ lapply (H1 ?) | lapply (H2 ?) ] -H1 -H2
/2 width=1 by cpys_flat/ -H
#H elim (cpys_inv_flat1 … H) -H
#X #Y #H1 #H2 #H destruct //
qed-.

(* Basic inversion lemmas ***************************************************)

lemma lleq_inv_bind: ∀a,I,L1,L2,V,T,d. L1 ⋕[ⓑ{a,I}V.T, d] L2 →
                     L1 ⋕[V, d] L2 ∧ L1.ⓑ{I}V ⋕[T, ⫯d] L2.ⓑ{I}V.
/3 width=4 by lleq_fwd_bind_sn, lleq_fwd_bind_dx, conj/ qed-.

lemma lleq_inv_flat: ∀I,L1,L2,V,T,d. L1 ⋕[ⓕ{I}V.T, d] L2 →
                     L1 ⋕[V, d] L2 ∧ L1 ⋕[T, d] L2.
/3 width=3 by lleq_fwd_flat_sn, lleq_fwd_flat_dx, conj/ qed-.

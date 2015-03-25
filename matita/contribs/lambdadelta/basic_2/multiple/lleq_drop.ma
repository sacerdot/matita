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

include "basic_2/multiple/llpx_sn_drop.ma".
include "basic_2/multiple/lleq.ma".

(* LAZY EQUIVALENCE FOR LOCAL ENVIRONMENTS **********************************)

(* Advanced properties ******************************************************)

lemma lleq_bind_repl_O: ∀I,L1,L2,V,T. L1.ⓑ{I}V ≡[T, 0] L2.ⓑ{I}V →
                        ∀J,W. L1 ≡[W, 0] L2 → L1.ⓑ{J}W ≡[T, 0] L2.ⓑ{J}W.
/2 width=7 by llpx_sn_bind_repl_O/ qed-.

lemma lleq_dec: ∀T,L1,L2,l. Decidable (L1 ≡[T, l] L2).
/3 width=1 by llpx_sn_dec, eq_term_dec/ qed-.

lemma lleq_llpx_sn_trans: ∀R. lleq_transitive R →
                          ∀L1,L2,T,l. L1 ≡[T, l] L2 →
                          ∀L. llpx_sn R l T L2 L → llpx_sn R l T L1 L.
#R #HR #L1 #L2 #T #l #H @(lleq_ind … H) -L1 -L2 -T -l
[1,2,5: /4 width=6 by llpx_sn_fwd_length, llpx_sn_gref, llpx_sn_skip, llpx_sn_sort, trans_eq/
|4: /4 width=6 by llpx_sn_fwd_length, llpx_sn_free, le_repl_sn_conf_aux, trans_eq/
| #I #L1 #L2 #K1 #K2 #V #l #i #Hli #HLK1 #HLK2 #HK12 #IHK12 #L #H elim (llpx_sn_inv_lref_ge_sn … H … HLK2) -H -HLK2
  /3 width=11 by llpx_sn_lref/
| #a #I #L1 #L2 #V #T #l #_ #_ #IHV #IHT #L #H elim (llpx_sn_inv_bind … H) -H
  /3 width=1 by llpx_sn_bind/
| #I #L1 #L2 #V #T #l #_ #_ #IHV #IHT #L #H elim (llpx_sn_inv_flat … H) -H
  /3 width=1 by llpx_sn_flat/
]
qed-.

lemma lleq_llpx_sn_conf: ∀R. lleq_transitive R →
                         ∀L1,L2,T,l. L1 ≡[T, l] L2 →
                         ∀L. llpx_sn R l T L1 L → llpx_sn R l T L2 L.
/3 width=3 by lleq_llpx_sn_trans, lleq_sym/ qed-.

(* Advanced inversion lemmas ************************************************)

lemma lleq_inv_lref_ge_dx: ∀L1,L2,l,i. L1 ≡[#i, l] L2 → l ≤ i →
                           ∀I,K2,V. ⬇[i] L2 ≡ K2.ⓑ{I}V →
                           ∃∃K1. ⬇[i] L1 ≡ K1.ⓑ{I}V & K1 ≡[V, 0] K2.
#L1 #L2 #l #i #H #Hli #I #K2 #V #HLK2 elim (llpx_sn_inv_lref_ge_dx … H … HLK2) -L2
/2 width=3 by ex2_intro/
qed-.

lemma lleq_inv_lref_ge_sn: ∀L1,L2,l,i. L1 ≡[#i, l] L2 → l ≤ i →
                           ∀I,K1,V. ⬇[i] L1 ≡ K1.ⓑ{I}V →
                           ∃∃K2. ⬇[i] L2 ≡ K2.ⓑ{I}V & K1 ≡[V, 0] K2.
#L1 #L2 #l #i #H #Hli #I1 #K1 #V #HLK1 elim (llpx_sn_inv_lref_ge_sn … H … HLK1) -L1
/2 width=3 by ex2_intro/
qed-.

lemma lleq_inv_lref_ge_bi: ∀L1,L2,l,i. L1 ≡[#i, l] L2 → l ≤ i →
                           ∀I1,I2,K1,K2,V1,V2.
                           ⬇[i] L1 ≡ K1.ⓑ{I1}V1 → ⬇[i] L2 ≡ K2.ⓑ{I2}V2 →
                           ∧∧ I1 = I2 & K1 ≡[V1, 0] K2 & V1 = V2.
/2 width=8 by llpx_sn_inv_lref_ge_bi/ qed-.

lemma lleq_inv_lref_ge: ∀L1,L2,l,i. L1 ≡[#i, l] L2 → l ≤ i →
                        ∀I,K1,K2,V. ⬇[i] L1 ≡ K1.ⓑ{I}V → ⬇[i] L2 ≡ K2.ⓑ{I}V →
                        K1 ≡[V, 0] K2.
#L1 #L2 #l #i #HL12 #Hli #I #K1 #K2 #V #HLK1 #HLK2
elim (lleq_inv_lref_ge_bi … HL12 … HLK1 HLK2) //
qed-.

lemma lleq_inv_S: ∀L1,L2,T,l. L1 ≡[T, l+1] L2 →
                  ∀I,K1,K2,V. ⬇[l] L1 ≡ K1.ⓑ{I}V → ⬇[l] L2 ≡ K2.ⓑ{I}V →
                  K1 ≡[V, 0] K2 → L1 ≡[T, l] L2.
/2 width=9 by llpx_sn_inv_S/ qed-.

lemma lleq_inv_bind_O: ∀a,I,L1,L2,V,T. L1 ≡[ⓑ{a,I}V.T, 0] L2 →
                       L1 ≡[V, 0] L2 ∧ L1.ⓑ{I}V ≡[T, 0] L2.ⓑ{I}V.
/2 width=2 by llpx_sn_inv_bind_O/ qed-.

(* Advanced forward lemmas **************************************************)

lemma lleq_fwd_lref_dx: ∀L1,L2,l,i. L1 ≡[#i, l] L2 →
                        ∀I,K2,V. ⬇[i] L2 ≡ K2.ⓑ{I}V →
                        i < l ∨
                        ∃∃K1. ⬇[i] L1 ≡ K1.ⓑ{I}V & K1 ≡[V, 0] K2 & l ≤ i.
#L1 #L2 #l #i #H #I #K2 #V #HLK2 elim (llpx_sn_fwd_lref_dx … H … HLK2) -L2
[ | * ] /3 width=3 by ex3_intro, or_intror, or_introl/
qed-.

lemma lleq_fwd_lref_sn: ∀L1,L2,l,i. L1 ≡[#i, l] L2 →
                        ∀I,K1,V. ⬇[i] L1 ≡ K1.ⓑ{I}V →
                        i < l ∨
                        ∃∃K2. ⬇[i] L2 ≡ K2.ⓑ{I}V & K1 ≡[V, 0] K2 & l ≤ i.
#L1 #L2 #l #i #H #I #K1 #V #HLK1 elim (llpx_sn_fwd_lref_sn … H … HLK1) -L1
[ | * ] /3 width=3 by ex3_intro, or_intror, or_introl/
qed-.

lemma lleq_fwd_bind_O_dx: ∀a,I,L1,L2,V,T. L1 ≡[ⓑ{a,I}V.T, 0] L2 →
                          L1.ⓑ{I}V ≡[T, 0] L2.ⓑ{I}V.
/2 width=2 by llpx_sn_fwd_bind_O_dx/ qed-.

(* Properties on relocation *************************************************)

lemma lleq_lift_le: ∀K1,K2,T,lt. K1 ≡[T, lt] K2 →
                    ∀L1,L2,l,m. ⬇[Ⓕ, l, m] L1 ≡ K1 → ⬇[Ⓕ, l, m] L2 ≡ K2 →
                    ∀U. ⬆[l, m] T ≡ U → lt ≤ l → L1 ≡[U, lt] L2.
/3 width=10 by llpx_sn_lift_le, lift_mono/ qed-.

lemma lleq_lift_ge: ∀K1,K2,T,lt. K1 ≡[T, lt] K2 →
                    ∀L1,L2,l,m. ⬇[Ⓕ, l, m] L1 ≡ K1 → ⬇[Ⓕ, l, m] L2 ≡ K2 →
                    ∀U. ⬆[l, m] T ≡ U → l ≤ lt → L1 ≡[U, lt+m] L2.
/2 width=9 by llpx_sn_lift_ge/ qed-.

(* Inversion lemmas on relocation *******************************************)

lemma lleq_inv_lift_le: ∀L1,L2,U,lt. L1 ≡[U, lt] L2 →
                        ∀K1,K2,l,m. ⬇[Ⓕ, l, m] L1 ≡ K1 → ⬇[Ⓕ, l, m] L2 ≡ K2 →
                        ∀T. ⬆[l, m] T ≡ U → lt ≤ l → K1 ≡[T, lt] K2.
/3 width=10 by llpx_sn_inv_lift_le, ex2_intro/ qed-.

lemma lleq_inv_lift_be: ∀L1,L2,U,lt. L1 ≡[U, lt] L2 →
                        ∀K1,K2,l,m. ⬇[Ⓕ, l, m] L1 ≡ K1 → ⬇[Ⓕ, l, m] L2 ≡ K2 →
                        ∀T. ⬆[l, m] T ≡ U → l ≤ lt → lt ≤ l + m → K1 ≡[T, l] K2.
/2 width=11 by llpx_sn_inv_lift_be/ qed-.

lemma lleq_inv_lift_ge: ∀L1,L2,U,lt. L1 ≡[U, lt] L2 →
                        ∀K1,K2,l,m. ⬇[Ⓕ, l, m] L1 ≡ K1 → ⬇[Ⓕ, l, m] L2 ≡ K2 →
                        ∀T. ⬆[l, m] T ≡ U → l + m ≤ lt → K1 ≡[T, lt-m] K2.
/2 width=9 by llpx_sn_inv_lift_ge/ qed-.

(* Inversion lemmas on negated lazy quivalence for local environments *******)

lemma nlleq_inv_bind: ∀a,I,L1,L2,V,T,l. (L1 ≡[ⓑ{a,I}V.T, l] L2 → ⊥) →
                      (L1 ≡[V, l] L2 → ⊥) ∨ (L1.ⓑ{I}V ≡[T, ⫯l] L2.ⓑ{I}V → ⊥).
/3 width=2 by nllpx_sn_inv_bind, eq_term_dec/ qed-.

lemma nlleq_inv_flat: ∀I,L1,L2,V,T,l. (L1 ≡[ⓕ{I}V.T, l] L2 → ⊥) →
                      (L1 ≡[V, l] L2 → ⊥) ∨ (L1 ≡[T, l] L2 → ⊥).
/3 width=2 by nllpx_sn_inv_flat, eq_term_dec/ qed-.

lemma nlleq_inv_bind_O: ∀a,I,L1,L2,V,T. (L1 ≡[ⓑ{a,I}V.T, 0] L2 → ⊥) →
                        (L1 ≡[V, 0] L2 → ⊥) ∨ (L1.ⓑ{I}V ≡[T, 0] L2.ⓑ{I}V → ⊥).
/3 width=2 by nllpx_sn_inv_bind_O, eq_term_dec/ qed-.

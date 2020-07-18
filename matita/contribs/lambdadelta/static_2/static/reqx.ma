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

include "static_2/notation/relations/approxeqsn_3.ma".
include "static_2/syntax/teqx_ext.ma".
include "static_2/static/reqg.ma".

(* SORT-IRRELEVANT EQUIVALENCE FOR LOCAL ENVIRONMENTS ON REFERRED ENTRIES ***)
(*
definition reqx: relation3 … ≝
           reqg sfull.
*)
interpretation
  "sort-irrelevant equivalence on referred entries (local environment)"
  'ApproxEqSn T L1 L2 = (reqg sfull T L1 L2).

interpretation
  "sort-irrelevant ranged equivalence (local environment)"
  'StarEqSn f L1 L2 = (sex ceqx_ext cfull f L1 L2).

(* Basic properties ***********************************************************)
(*
lemma frees_teqx_conf_reqx:
      ∀f,L1,T1. L1 ⊢ 𝐅+❪T1❫ ≘ f → ∀T2. T1 ≛ T2 →
      ∀L2. L1 ≛[f] L2 → L2 ⊢ 𝐅+❪T2❫ ≘ f.
#f #L1 #T1 #H elim H -f -L1 -T1
[ #f #L1 #s1 #Hf #X #H1 #L2 #_
  elim (teqx_inv_sort1 … H1) -H1 #s2 #H destruct
  /2 width=3 by frees_sort/
| #f #i #Hf #X #H1
  >(teqx_inv_lref1 … H1) -X #Y #H2
  >(sex_inv_atom1 … H2) -Y
  /2 width=1 by frees_atom/
| #f #I #L1 #V1 #_ #IH #X #H1
  >(teqx_inv_lref1 … H1) -X #Y #H2
  elim (sex_inv_next1 … H2) -H2 #Z #L2 #HL12 #HZ #H destruct
  elim (ext2_inv_pair_sn … HZ) -HZ #V2 #HV12 #H destruct
  /3 width=1 by frees_pair/
| #f #I #L1 #Hf #X #H1
  >(teqx_inv_lref1 … H1) -X #Y #H2
  elim (sex_inv_next1 … H2) -H2 #Z #L2 #_ #HZ #H destruct
  >(ext2_inv_unit_sn … HZ) -Z /2 width=1 by frees_unit/
| #f #I #L1 #i #_ #IH #X #H1
  >(teqx_inv_lref1 … H1) -X #Y #H2
  elim (sex_inv_push1 … H2) -H2 #J #L2 #HL12 #_ #H destruct
  /3 width=1 by frees_lref/
| #f #L1 #l #Hf #X #H1 #L2 #_
  >(teqx_inv_gref1 … H1) -X /2 width=1 by frees_gref/
| #f1V #f1T #f1 #p #I #L1 #V1 #T1 #_ #_ #Hf1 #IHV #IHT #X #H1
  elim (teqx_inv_pair1 … H1) -H1 #V2 #T2 #HV12 #HT12 #H1 #L2 #HL12 destruct
  /6 width=5 by frees_bind, sex_inv_tl, ext2_pair, sle_sex_trans, sor_inv_sle_dx, sor_inv_sle_sn/
| #f1V #f1T #f1 #I #L1 #V1 #T1 #_ #_ #Hf1 #IHV #IHT #X #H1
  elim (teqx_inv_pair1 … H1) -H1 #V2 #T2 #HV12 #HT12 #H1 #L2 #HL12 destruct
  /5 width=5 by frees_flat, sle_sex_trans, sor_inv_sle_dx, sor_inv_sle_sn/
]
qed-.

lemma frees_teqx_conf:
      ∀f,L,T1. L ⊢ 𝐅+❪T1❫ ≘ f →
      ∀T2. T1 ≛ T2 → L ⊢ 𝐅+❪T2❫ ≘ f.
/4 width=7 by frees_teqx_conf_reqx, sex_refl, ext2_refl/ qed-.

lemma frees_reqx_conf:
      ∀f,L1,T. L1 ⊢ 𝐅+❪T❫ ≘ f →
      ∀L2. L1 ≛[f] L2 → L2 ⊢ 𝐅+❪T❫ ≘ f.
/2 width=7 by frees_teqx_conf_reqx, teqx_refl/ qed-.

lemma teqx_rex_conf_sn (R):
      s_r_confluent1 … cdeq (rex R).
#R #L1 #T1 #T2 #HT12 #L2 *
/3 width=5 by frees_teqx_conf, ex2_intro/
qed-.

lemma teqx_rex_div (R):
      ∀T1,T2. T1 ≛ T2 →
      ∀L1,L2. L1 ⪤[R,T2] L2 → L1 ⪤[R,T1] L2.
/3 width=5 by teqx_rex_conf_sn, teqx_sym/ qed-.

lemma teqx_reqx_conf_sn:
      s_r_confluent1 … cdeq reqx.
/2 width=5 by teqx_rex_conf_sn/ qed-.

lemma teqx_reqx_div:
      ∀T1,T2. T1 ≛ T2 →
      ∀L1,L2. L1 ≛[T2] L2 → L1 ≛[T1] L2.
/2 width=5 by teqx_rex_div/ qed-.

lemma reqx_atom: ∀I. ⋆ ≛[⓪[I]] ⋆.
/2 width=1 by rex_atom/ qed.

lemma reqx_sort:
      ∀I1,I2,L1,L2,s.
      L1 ≛[⋆s] L2 → L1.ⓘ[I1] ≛[⋆s] L2.ⓘ[I2].
/2 width=1 by rex_sort/ qed.

lemma reqx_pair:
      ∀I,L1,L2,V1,V2.
      L1 ≛[V1] L2 → V1 ≛ V2 → L1.ⓑ[I]V1 ≛[#0] L2.ⓑ[I]V2.
/2 width=1 by rex_pair/ qed.

lemma reqx_unit:
      ∀f,I,L1,L2. 𝐈❪f❫ → L1 ≛[f] L2 →
      L1.ⓤ[I] ≛[#0] L2.ⓤ[I].
/2 width=3 by rex_unit/ qed.

lemma reqx_lref:
      ∀I1,I2,L1,L2,i.
      L1 ≛[#i] L2 → L1.ⓘ[I1] ≛[#↑i] L2.ⓘ[I2].
/2 width=1 by rex_lref/ qed.

lemma reqx_gref:
      ∀I1,I2,L1,L2,l.
      L1 ≛[§l] L2 → L1.ⓘ[I1] ≛[§l] L2.ⓘ[I2].
/2 width=1 by rex_gref/ qed.

lemma reqx_bind_repl_dx:
      ∀I,I1,L1,L2.∀T:term. L1.ⓘ[I] ≛[T] L2.ⓘ[I1] →
      ∀I2. I ≛ I2 → L1.ⓘ[I] ≛[T] L2.ⓘ[I2].
/2 width=2 by rex_bind_repl_dx/ qed-.
*)
lemma reqg_reqx (S) (T):
      ∀L1,L2. L1 ≛[S,T] L2 → L1 ≅[T] L2.
/2 width=3 by reqg_co/ qed.
(*
(* Basic inversion lemmas ***************************************************)

lemma reqx_inv_atom_sn:
      ∀Y2. ∀T:term. ⋆ ≛[T] Y2 → Y2 = ⋆.
/2 width=3 by rex_inv_atom_sn/ qed-.

lemma reqx_inv_atom_dx:
      ∀Y1. ∀T:term. Y1 ≛[T] ⋆ → Y1 = ⋆.
/2 width=3 by rex_inv_atom_dx/ qed-.

lemma reqx_inv_zero:
      ∀Y1,Y2. Y1 ≛[#0] Y2 →
      ∨∨ ∧∧ Y1 = ⋆ & Y2 = ⋆
       | ∃∃I,L1,L2,V1,V2. L1 ≛[V1] L2 & V1 ≛ V2 & Y1 = L1.ⓑ[I]V1 & Y2 = L2.ⓑ[I]V2
       | ∃∃f,I,L1,L2. 𝐈❪f❫ & L1 ≛[f] L2 & Y1 = L1.ⓤ[I] & Y2 = L2.ⓤ[I].
#Y1 #Y2 #H elim (rex_inv_zero … H) -H *
/3 width=9 by or3_intro0, or3_intro1, or3_intro2, ex4_5_intro, ex4_4_intro, conj/
qed-.

lemma reqx_inv_lref:
      ∀Y1,Y2,i. Y1 ≛[#↑i] Y2 →
      ∨∨ ∧∧ Y1 = ⋆ & Y2 = ⋆
       | ∃∃I1,I2,L1,L2. L1 ≛[#i] L2 & Y1 = L1.ⓘ[I1] & Y2 = L2.ⓘ[I2].
/2 width=1 by rex_inv_lref/ qed-.

(* Basic_2A1: uses: lleq_inv_bind lleq_inv_bind_O *)
lemma reqx_inv_bind:
      ∀p,I,L1,L2,V,T. L1 ≛[ⓑ[p,I]V.T] L2 →
      ∧∧ L1 ≛[V] L2 & L1.ⓑ[I]V ≛[T] L2.ⓑ[I]V.
/2 width=2 by rex_inv_bind/ qed-.

(* Basic_2A1: uses: lleq_inv_flat *)
lemma reqx_inv_flat:
      ∀I,L1,L2,V,T. L1 ≛[ⓕ[I]V.T] L2 →
      ∧∧ L1 ≛[V] L2 & L1 ≛[T] L2.
/2 width=2 by rex_inv_flat/ qed-.

(* Advanced inversion lemmas ************************************************)

lemma reqx_inv_zero_pair_sn:
      ∀I,Y2,L1,V1. L1.ⓑ[I]V1 ≛[#0] Y2 →
      ∃∃L2,V2. L1 ≛[V1] L2 & V1 ≛ V2 & Y2 = L2.ⓑ[I]V2.
/2 width=1 by rex_inv_zero_pair_sn/ qed-.

lemma reqx_inv_zero_pair_dx:
      ∀I,Y1,L2,V2. Y1 ≛[#0] L2.ⓑ[I]V2 →
      ∃∃L1,V1. L1 ≛[V1] L2 & V1 ≛ V2 & Y1 = L1.ⓑ[I]V1.
/2 width=1 by rex_inv_zero_pair_dx/ qed-.

lemma reqx_inv_lref_bind_sn:
      ∀I1,Y2,L1,i. L1.ⓘ[I1] ≛[#↑i] Y2 →
      ∃∃I2,L2. L1 ≛[#i] L2 & Y2 = L2.ⓘ[I2].
/2 width=2 by rex_inv_lref_bind_sn/ qed-.

lemma reqx_inv_lref_bind_dx:
      ∀I2,Y1,L2,i. Y1 ≛[#↑i] L2.ⓘ[I2] →
      ∃∃I1,L1. L1 ≛[#i] L2 & Y1 = L1.ⓘ[I1].
/2 width=2 by rex_inv_lref_bind_dx/ qed-.

(* Basic forward lemmas *****************************************************)

lemma reqx_fwd_zero_pair:
      ∀I,K1,K2,V1,V2.
      K1.ⓑ[I]V1 ≛[#0] K2.ⓑ[I]V2 → K1 ≛[V1] K2.
/2 width=3 by rex_fwd_zero_pair/ qed-.

(* Basic_2A1: uses: lleq_fwd_bind_sn lleq_fwd_flat_sn *)
lemma reqx_fwd_pair_sn:
      ∀I,L1,L2,V,T. L1 ≛[②[I]V.T] L2 → L1 ≛[V] L2.
/2 width=3 by rex_fwd_pair_sn/ qed-.

(* Basic_2A1: uses: lleq_fwd_bind_dx lleq_fwd_bind_O_dx *)
lemma reqx_fwd_bind_dx:
      ∀p,I,L1,L2,V,T.
      L1 ≛[ⓑ[p,I]V.T] L2 → L1.ⓑ[I]V ≛[T] L2.ⓑ[I]V.
/2 width=2 by rex_fwd_bind_dx/ qed-.

(* Basic_2A1: uses: lleq_fwd_flat_dx *)
lemma reqx_fwd_flat_dx:
      ∀I,L1,L2,V,T. L1 ≛[ⓕ[I]V.T] L2 → L1 ≛[T] L2.
/2 width=3 by rex_fwd_flat_dx/ qed-.

lemma reqx_fwd_dx:
      ∀I2,L1,K2. ∀T:term. L1 ≛[T] K2.ⓘ[I2] →
      ∃∃I1,K1. L1 = K1.ⓘ[I1].
/2 width=5 by rex_fwd_dx/ qed-.
*)

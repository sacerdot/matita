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

include "static_2/notation/relations/ideqsn_3.ma".
include "static_2/syntax/teq_ext.ma".
include "static_2/static/reqg.ma".

(* SYNTACTIC EQUIVALENCE FOR LOCAL ENVIRONMENTS ON REFERRED ENTRIES *********)

(* Basic_2A1: was: lleq *)
definition req: relation3 term lenv lenv ≝
           reqg (eq …).

interpretation
  "syntactic equivalence on referred entries (local environment)"
  'IdEqSn T L1 L2 = (req T L1 L2).

(* Note: "R_transitive_req R" is equivalent to "R_transitive_rex ceq R R" *)
(* Basic_2A1: uses: lleq_transitive *)
definition R_transitive_req: predicate (relation3 lenv term term) ≝
           λR. ∀L2,T1,T2. R L2 T1 T2 → ∀L1. L1 ≡[T1] L2 → R L1 T1 T2.

(* Basic inversion lemmas ***************************************************)

lemma req_inv_bind:
      ∀p,I,L1,L2,V,T. L1 ≡[ⓑ[p,I]V.T] L2 →
      ∧∧ L1 ≡[V] L2 & L1.ⓑ[I]V ≡[T] L2.ⓑ[I]V.
/2 width=2 by reqg_inv_bind_refl/ qed-.

lemma req_inv_flat:
      ∀I,L1,L2,V,T. L1 ≡[ⓕ[I]V.T] L2 →
      ∧∧ L1 ≡[V] L2 & L1 ≡[T] L2.
/2 width=2 by reqg_inv_flat/ qed-.

(* Advanced inversion lemmas ************************************************)

lemma req_inv_zero_pair_sn:
      ∀I,L2,K1,V. K1.ⓑ[I]V ≡[#0] L2 →
      ∃∃K2. K1 ≡[V] K2 & L2 = K2.ⓑ[I]V.
#I #L2 #K1 #V #H
elim (reqg_inv_zero_pair_sn … H) -H #K2 #X #HK12 #HX #H destruct
@(teq_repl_1 … HX) -X
@(ex2_intro … HK12) // (**) (* auto fails because a δ-expamsion gets in the way *)
qed-.

lemma req_inv_zero_pair_dx:
      ∀I,L1,K2,V. L1 ≡[#0] K2.ⓑ[I]V →
      ∃∃K1. K1 ≡[V] K2 & L1 = K1.ⓑ[I]V.
#I #L1 #K2 #V #H
elim (reqg_inv_zero_pair_dx … H) -H #K1 #X #HK12 #HX #H destruct
@(teq_repl_1 … HX) -V
@(ex2_intro … HK12) // (**) (* auto fails because a δ-expamsion gets in the way *)
qed-.

lemma req_inv_lref_bind_sn:
      ∀I1,K1,L2,i. K1.ⓘ[I1] ≡[#↑i] L2 →
      ∃∃I2,K2. K1 ≡[#i] K2 & L2 = K2.ⓘ[I2].
/2 width=2 by reqg_inv_lref_bind_sn/ qed-.

lemma req_inv_lref_bind_dx:
      ∀I2,K2,L1,i. L1 ≡[#↑i] K2.ⓘ[I2] →
      ∃∃I1,K1. K1 ≡[#i] K2 & L1 = K1.ⓘ[I1].
/2 width=2 by reqg_inv_lref_bind_dx/ qed-.

(* Basic forward lemmas *****************************************************)

(* Basic_2A1: was: llpx_sn_lrefl *)
(* Basic_2A1: this should have been lleq_fwd_llpx_sn *)
lemma req_fwd_rex (R):
      c_reflexive … R →
      ∀L1,L2,T. L1 ≡[T] L2 → L1 ⪤[R,T] L2.
#R #HR #L1 #L2 #T * #f #Hf #HL12
/5 width=7 by sex_co, cext2_co, teq_repl_1, ex2_intro/
qed-.

lemma req_fwd_reqg (S) (T:term):
      reflexive … S →
      ∀L1,L2. L1 ≡[T] L2 → L1 ≛[S,T] L2.
/3 width=1 by req_fwd_rex, teqg_refl/ qed-.

lemma transitive_req_fwd_rex (R):
      R_transitive_req R → R_transitive_rex ceq R R.
#R #HR #L1 #L #T1 #HL1 #T #HT #T2 #HT2
@(HR … HL1) -HR -HL1 >(teq_inv_eq … HT) -T1 // (**)
qed-.

(* Basic_2A1: removed theorems 10:
              lleq_ind lleq_fwd_lref
              lleq_fwd_drop_sn lleq_fwd_drop_dx
              lleq_skip lleq_lref lleq_free
              lleq_Y lleq_ge_up lleq_ge

*)

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

include "static_2/syntax/ext2_ext2.ma".
include "static_2/syntax/teqg_teqg.ma".
include "static_2/static/rex_rex.ma".
include "static_2/static/reqg_length.ma".

(* GENERIC EQUIVALENCE FOR LOCAL ENVIRONMENTS ON REFERRED ENTRIES ***********)

(* Advanced forward lemmas **************************************************)

lemma frees_reqg_conf (S):
      reflexive … S →
      ∀f,L1,T. L1 ⊢ 𝐅+❪T❫ ≘ f →
      ∀L2. L1 ≛[S,T] L2 → L2 ⊢ 𝐅+❪T❫ ≘ f.
/3 width=7 by frees_seqg_conf, rex_inv_frees/ qed-.

(* Properties with free variables inclusion for restricted closures *******)

lemma reqg_fsle_comp (S):
      reflexive … S →
      rex_fsle_compatible (ceqg S).
#S #HS #L1 #L2 #T #HL12
elim (frees_total L1 T) #f #Hf
/4 width=8 by frees_reqg_conf, rex_fwd_length, lveq_length_eq, sle_refl, ex4_4_intro/
qed.

(* Advanced properties ******************************************************)

lemma reqg_sym (S) (T):
      reflexive … S → symmetric … S →
      symmetric … (reqg S T).
/3 width=3 by reqg_fsge_comp, rex_sym, teqg_sym/ qed-.

(* Basic_2A1: uses: lleq_dec *)
lemma reqg_dec (S):
      (∀s1,s2. Decidable … (S s1 s2)) →
      ∀L1,L2. ∀T:term. Decidable (L1 ≛[S,T] L2).
/3 width=1 by rex_dec, teqg_dec/ qed-.

(* Main properties **********************************************************)

(* Basic_2A1: uses: lleq_bind lleq_bind_O *)
theorem reqg_bind (S):
        ∀p,I,L1,L2,V1,V2,T.
        L1 ≛[S,V1] L2 → L1.ⓑ[I]V1 ≛[S,T] L2.ⓑ[I]V2 →
        L1 ≛[S,ⓑ[p,I]V1.T] L2.
/2 width=2 by rex_bind/ qed.

(* Basic_2A1: uses: lleq_flat *)
theorem reqg_flat (S):
        ∀I,L1,L2,V,T.
        L1 ≛[S,V] L2 → L1 ≛[S,T] L2 → L1 ≛[S,ⓕ[I]V.T] L2.
/2 width=1 by rex_flat/ qed.

theorem reqg_bind_void (S):
        ∀p,I,L1,L2,V,T.
        L1 ≛[S,V] L2 → L1.ⓧ ≛[S,T] L2.ⓧ → L1 ≛[S,ⓑ[p,I]V.T] L2.
/2 width=1 by rex_bind_void/ qed.

(* Basic_2A1: uses: lleq_trans *)
theorem reqg_trans (S) (T):
        reflexive … S → Transitive … S →
        Transitive … (reqg S T).
#S #T #H1S #H2S #L1 #L * #f1 #Hf1 #HL1 #L2 * #f2 #Hf2 #HL2
lapply (frees_teqg_conf_seqg … Hf1 T … HL1) /2 width=1 by teqg_refl/ #H0
lapply (frees_mono … Hf2 … H0) -Hf2 -H0
/5 width=7 by sex_trans, sex_eq_repl_back, teqg_trans, ext2_trans, ex2_intro/
qed-.

(* Basic_2A1: uses: lleq_canc_sn *)
theorem reqg_canc_sn (S) (T):
        reflexive … S → symmetric … S → Transitive … S →
        left_cancellable … (reqg S T).
/3 width=3 by reqg_trans, reqg_sym/ qed-.

(* Basic_2A1: uses: lleq_canc_dx *)
theorem reqg_canc_dx (S) (T):
        reflexive … S → symmetric … S → Transitive … S →
        right_cancellable … (reqg S T).
/3 width=3 by reqg_trans, reqg_sym/ qed-.

theorem reqg_repl (S) (T:term):
        reflexive … S → symmetric … S → Transitive … S → 
        ∀L1,L2. L1 ≛[S,T] L2 →
        ∀K1. L1 ≛[S,T] K1 → ∀K2. L2 ≛[S,T] K2 → K1 ≛[S,T] K2.
/3 width=3 by reqg_canc_sn, reqg_trans/ qed-.

(* Negated properties *******************************************************)

(* Note: auto works with /4 width=8/ so reqg_canc_sn is preferred **********)
(* Basic_2A1: uses: lleq_nlleq_trans *)
lemma reqg_rneqg_trans (S) (T:term):
      reflexive … S → symmetric … S → Transitive … S →
      ∀L1,L. L1 ≛[S,T] L →
      ∀L2. (L ≛[S,T] L2 → ⊥) → (L1 ≛[S,T] L2 → ⊥).
/3 width=3 by reqg_canc_sn/ qed-.

(* Basic_2A1: uses: nlleq_lleq_div *)
lemma rneqg_reqg_div (S) (T:term):
      reflexive … S → Transitive … S →
      ∀L2,L. L2 ≛[S,T] L →
      ∀L1. (L1 ≛[S,T] L → ⊥) → (L1 ≛[S,T] L2 → ⊥).
/3 width=3 by reqg_trans/ qed-.

theorem rneqg_reqg_canc_dx (S) (T:term):
        reflexive … S → Transitive … S →
        ∀L1,L. (L1 ≛[S,T] L → ⊥) →
        ∀L2. L2 ≛[S,T] L → L1 ≛[S,T] L2 → ⊥.
/3 width=3 by reqg_trans/ qed-.

(* Negated inversion lemmas *************************************************)

(* Basic_2A1: uses: nlleq_inv_bind nlleq_inv_bind_O *)
lemma rneqg_inv_bind (S):
      (∀s1,s2. Decidable … (S s1 s2)) →
      ∀p,I,L1,L2,V,T. (L1 ≛[S,ⓑ[p,I]V.T] L2 → ⊥) →
      ∨∨ L1 ≛[S,V] L2 → ⊥ | (L1.ⓑ[I]V ≛[S,T] L2.ⓑ[I]V → ⊥).
/3 width=2 by rnex_inv_bind, teqg_dec/ qed-.

(* Basic_2A1: uses: nlleq_inv_flat *)
lemma rneqg_inv_flat (S):
      (∀s1,s2. Decidable … (S s1 s2)) →
      ∀I,L1,L2,V,T. (L1 ≛[S,ⓕ[I]V.T] L2 → ⊥) →
      ∨∨ L1 ≛[S,V] L2 → ⊥ | (L1 ≛[S,T] L2 → ⊥).
/3 width=2 by rnex_inv_flat, teqg_dec/ qed-.

lemma rneqg_inv_bind_void (S):
      (∀s1,s2. Decidable … (S s1 s2)) →
      ∀p,I,L1,L2,V,T. (L1 ≛[S,ⓑ[p,I]V.T] L2 → ⊥) →
      ∨∨ L1 ≛[S,V] L2 → ⊥ | (L1.ⓧ ≛[S,T] L2.ⓧ → ⊥).
/3 width=3 by rnex_inv_bind_void, teqg_dec/ qed-.

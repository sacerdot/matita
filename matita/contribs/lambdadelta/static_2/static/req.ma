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
include "static_2/static/rex.ma".

(* SYNTACTIC EQUIVALENCE FOR LOCAL ENVIRONMENTS ON REFERRED ENTRIES *********)

(* Basic_2A1: was: lleq *)
definition req: relation3 term lenv lenv ≝
                rex ceq.

interpretation
   "syntactic equivalence on referred entries (local environment)"
   'IdEqSn T L1 L2 = (req T L1 L2).

(* Note: "req_transitive R" is equivalent to "rex_transitive ceq R R" *)
(* Basic_2A1: uses: lleq_transitive *)
definition req_transitive: predicate (relation3 lenv term term) ≝
           λR. ∀L2,T1,T2. R L2 T1 T2 → ∀L1. L1 ≡[T1] L2 → R L1 T1 T2.

(* Basic inversion lemmas ***************************************************)

lemma req_inv_bind: ∀p,I,L1,L2,V,T. L1 ≡[ⓑ{p,I}V.T] L2 →
                    ∧∧ L1 ≡[V] L2 & L1.ⓑ{I}V ≡[T] L2.ⓑ{I}V.
/2 width=2 by rex_inv_bind/ qed-.

lemma req_inv_flat: ∀I,L1,L2,V,T. L1 ≡[ⓕ{I}V.T] L2 →
                    ∧∧ L1 ≡[V] L2 & L1 ≡[T] L2.
/2 width=2 by rex_inv_flat/ qed-.

(* Advanced inversion lemmas ************************************************)

lemma req_inv_zero_pair_sn: ∀I,L2,K1,V. K1.ⓑ{I}V ≡[#0] L2 →
                            ∃∃K2. K1 ≡[V] K2 & L2 = K2.ⓑ{I}V.
#I #L2 #K1 #V #H
elim (rex_inv_zero_pair_sn … H) -H #K2 #X #HK12 #HX #H destruct
/2 width=3 by ex2_intro/
qed-.

lemma req_inv_zero_pair_dx: ∀I,L1,K2,V. L1 ≡[#0] K2.ⓑ{I}V →
                            ∃∃K1. K1 ≡[V] K2 & L1 = K1.ⓑ{I}V.
#I #L1 #K2 #V #H
elim (rex_inv_zero_pair_dx … H) -H #K1 #X #HK12 #HX #H destruct
/2 width=3 by ex2_intro/
qed-.

lemma req_inv_lref_bind_sn: ∀I1,K1,L2,i. K1.ⓘ{I1} ≡[#↑i] L2 →
                            ∃∃I2,K2. K1 ≡[#i] K2 & L2 = K2.ⓘ{I2}.
/2 width=2 by rex_inv_lref_bind_sn/ qed-.

lemma req_inv_lref_bind_dx: ∀I2,K2,L1,i. L1 ≡[#↑i] K2.ⓘ{I2} →
                            ∃∃I1,K1. K1 ≡[#i] K2 & L1 = K1.ⓘ{I1}.
/2 width=2 by rex_inv_lref_bind_dx/ qed-.

(* Basic forward lemmas *****************************************************)

(* Basic_2A1: was: llpx_sn_lrefl *)
(* Basic_2A1: this should have been lleq_fwd_llpx_sn *)
lemma req_fwd_rex: ∀R. c_reflexive … R →
                   ∀L1,L2,T. L1 ≡[T] L2 → L1 ⪤[R,T] L2.
#R #HR #L1 #L2 #T * #f #Hf #HL12
/4 width=7 by sex_co, cext2_co, ex2_intro/
qed-.

(* Basic_properties *********************************************************)

lemma frees_req_conf: ∀f,L1,T. L1 ⊢ 𝐅+⦃T⦄ ≘ f →
                      ∀L2. L1 ≡[T] L2 → L2 ⊢ 𝐅+⦃T⦄ ≘ f.
#f #L1 #T #H elim H -f -L1 -T
[ /2 width=3 by frees_sort/
| #f #i #Hf #L2 #H2
  >(rex_inv_atom_sn … H2) -L2
  /2 width=1 by frees_atom/
| #f #I #L1 #V1 #_ #IH #Y #H2
  elim (req_inv_zero_pair_sn … H2) -H2 #L2 #HL12 #H destruct
  /3 width=1 by frees_pair/
| #f #I #L1 #Hf #Y #H2
  elim (rex_inv_zero_unit_sn … H2) -H2 #g #L2 #_ #_ #H destruct
  /2 width=1 by frees_unit/
| #f #I #L1 #i #_ #IH #Y #H2
  elim (req_inv_lref_bind_sn … H2) -H2 #J #L2 #HL12 #H destruct
  /3 width=1 by frees_lref/
| /2 width=1 by frees_gref/
| #f1V #f1T #f1 #p #I #L1 #V1 #T1 #_ #_ #Hf1 #IHV #IHT #L2 #H2
  elim (req_inv_bind … H2) -H2 /3 width=5 by frees_bind/
| #f1V #f1T #f1 #I #L1 #V1 #T1 #_ #_ #Hf1 #IHV #IHT #L2 #H2
  elim (req_inv_flat … H2) -H2 /3 width=5 by frees_flat/
]
qed-.

(* Basic_2A1: removed theorems 10:
              lleq_ind lleq_fwd_lref
              lleq_fwd_drop_sn lleq_fwd_drop_dx
              lleq_skip lleq_lref lleq_free
              lleq_Y lleq_ge_up lleq_ge
               
*)

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

include "basic_2/notation/relations/lazyeqsn_3.ma".
include "basic_2/static/lfxs.ma".

(* SYNTACTIC EQUIVALENCE FOR LOCAL ENVIRONMENTS ON REFERRED ENTRIES *********)

(* Basic_2A1: was: lleq *)
definition lfeq: relation3 term lenv lenv ≝
                 lfxs ceq.

interpretation
   "syntactic equivalence on referred entries (local environment)"
   'LazyEqSn T L1 L2 = (lfeq T L1 L2).

(* Basic_2A1: uses: lleq_transitive *)
definition lfeq_transitive: predicate (relation3 lenv term term) ≝
           λR. ∀L2,T1,T2. R L2 T1 T2 → ∀L1. L1 ≡[T1] L2 → R L1 T1 T2.

(* Basic_properties *********************************************************)

lemma lfxs_transitive_lfeq: ∀R. lfxs_transitive ceq R R → lfeq_transitive R.
/2 width=5 by/ qed.

(* Basic inversion lemmas ***************************************************)

lemma lfeq_transitive_inv_lfxs: ∀R. lfeq_transitive R → lfxs_transitive ceq R R.
/2 width=3 by/ qed-.

(* Basic forward lemmas *****************************************************)

(* Basic_2A1: was: llpx_sn_lrefl *)
(* Note: this should have been lleq_fwd_llpx_sn *)
lemma lfeq_fwd_lfxs: ∀R. c_reflexive … R →
                     ∀L1,L2,T. L1 ≡[T] L2 → L1 ⪤*[R, T] L2.
#R #HR #L1 #L2 #T * #f #Hf #HL12
/4 width=7 by lexs_co, cext2_co, ex2_intro/
qed-.

(* Basic_2A1: removed theorems 10:
              lleq_ind lleq_fwd_lref
              lleq_fwd_drop_sn lleq_fwd_drop_dx
              lleq_skip lleq_lref lleq_free
              lleq_Y lleq_ge_up lleq_ge
               
*)

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

(***************************************************)

axiom lfeq_lfxs_trans: ∀R,L1,L,T. L1 ≡[T] L →
                       ∀L2. L ⪤*[R, T] L2 → L1 ⪤*[R, T] L2.

(* Basic_2A1: removed theorems 10:
              lleq_ind lleq_fwd_lref
              lleq_fwd_drop_sn lleq_fwd_drop_dx
              lleq_skip lleq_lref lleq_free
              lleq_Y lleq_ge_up lleq_ge
               
*)

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

include "static_2/static/reqg_reqg.ma".
include "static_2/static/req.ma".

(* SYNTACTIC EQUIVALENCE FOR LOCAL ENVIRONMENTS ON REFERRED ENTRIES *********)

(* Advanced Forward lemmas **************************************************)

lemma req_rex_trans (R) (L) (T):
      R_transitive_req R →
      ∀L1. L1 ≡[T] L → ∀L2. L ⪤[R,T] L2 → L1 ⪤[R,T] L2.
#R #L #T #HR #L1 #HL1 #L2 #HL2
@(rex_trans_fsle … HL1 … HL2) -L (**) (* fulll auto too slow *)
/3 width=16 by transitive_req_fwd_rex, reqg_fsle_comp, rex_trans_next/
qed-.

lemma req_reqg_trans (S) (T:term) (L):
      ∀L1. L1 ≡[T] L → ∀L2. L ≛[S,T] L2 → L1 ≛[S,T] L2.
/2 width=3 by req_rex_trans/ qed-.

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

include "basic_2/static/req_fsle.ma".
include "basic_2/static/rdeq.ma".

(* DEGREE-BASED EQUIVALENCE FOR LOCAL ENVIRONMENTS ON REFERRED ENTRIES ******)

(* Properties with syntactic equivalence on referred entries ****************)

lemma req_rdeq: ∀h,o,L1,L2. ∀T:term. L1 ≡[T] L2 → L1 ≛[h, o, T] L2.
/2 width=3 by rex_co/ qed.

lemma req_rdeq_trans: ∀h,o,L1,L. ∀T:term. L1 ≡[T] L →
                      ∀L2. L ≛[h, o, T] L2 → L1 ≛[h, o, T] L2.
/2 width=3 by req_rex_trans/ qed-.

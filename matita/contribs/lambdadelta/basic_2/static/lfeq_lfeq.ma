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

include "basic_2/static/lfxs_lfxs.ma".
include "basic_2/static/lfeq.ma".

(* SYNTACTIC EQUIVALENCE FOR LOCAL ENVIRONMENTS ON REFERRED ENTRIES *********)

(* Advanced forward lemmas **************************************************)

(* Note: the proof should may invoke lfeq_transitive_inv_lfxs *)
lemma lfeq_lfxs_trans: ∀R. c_reflexive … R → lfeq_transitive R →
                       ∀L1,L,T. L1 ≡[T] L →
                       ∀L2. L ⪤*[R, T] L2 → L1 ⪤*[R, T] L2.
/3 width=9 by lfxs_trans_gen/ qed-.

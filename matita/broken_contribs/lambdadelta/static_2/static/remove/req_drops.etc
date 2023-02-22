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

include "static_2/static/rex_drops.ma".
include "static_2/static/req.ma".

(* SYNTACTIC EQUIVALENCE FOR LOCAL ENVIRONMENTS ON REFERRED ENTRIES *********)

(* Note: req_inv_lifts_dx missing in basic_2A1 *)

(* Basic_2A1: uses: lleq_inv_lift_le lleq_inv_lift_be lleq_inv_lift_ge *)
lemma req_inv_lifts_bi: ∀L1,L2,U. L1 ≡[U] L2 → ∀b,f. 𝐔❪f❫ →
                        ∀K1,K2. ⇩*[b,f] L1 ≘ K1 → ⇩*[b,f] L2 ≘ K2 →
                        ∀T. ⇧*[f] T ≘ U → K1 ≡[T] K2.
/2 width=10 by rex_inv_lifts_bi/ qed-.

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

include "static_2/static/fdeq.ma".
include "static_2/static/aaa_rdeq.ma".

(* ATONIC ARITY ASSIGNMENT ON TERMS *****************************************)

(* Properties with sort-irrelevant equivalence on referred entries **********)

lemma aaa_fdeq_conf: ∀G1,G2,L1,L2,T1,T2. ⦃G1,L1,T1⦄ ≛ ⦃G2,L2,T2⦄ → 
                     ∀A. ⦃G1,L1⦄ ⊢ T1 ⁝ A → ⦃G2,L2⦄ ⊢ T2 ⁝ A.
#G1 #G2 #L1 #L2 #T1 #T2 * -G2 -L2 -T2
/2 width=5 by aaa_tdeq_conf_rdeq/ qed-.

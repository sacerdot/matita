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

include "basic_2/static/ffdeq.ma".
include "basic_2/static/aaa_lfdeq.ma".

(* ATONIC ARITY ASSIGNMENT ON TERMS *****************************************)

(* Properties with degree-based equivalence on referred entries *************)

lemma aaa_ffdeq_conf: ∀h,o,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ≛[h, o] ⦃G2, L2, T2⦄ → 
                      ∀A. ⦃G1, L1⦄ ⊢ T1 ⁝ A → ⦃G2, L2⦄ ⊢ T2 ⁝ A.
#h #o #G1 #G2 #L1 #L2 #T1 #T2 * -G2 -L2 -T2
/2 width=7 by aaa_tdeq_conf_lfdeq/ qed-.

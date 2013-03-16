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

include "basic_2/equivalence/lsubss_ssta.ma".
include "basic_2/dynamic/lsubsv.ma".

(* LOCAL ENVIRONMENT REFINEMENT FOR STRATIFIED NATIVE VALIDITY **************)

(* Properties on stratified static type assignment **************************)

lemma lsubsv_ssta_trans: ∀h,g,L2,T,U2,l. ⦃h, L2⦄ ⊢ T •[g] ⦃l, U2⦄ →
                         ∀L1. h ⊢ L1 ⊩:⊑[g] L2 →
                         ∃∃U1. ⦃h, L1⦄ ⊢ T •[g] ⦃l, U1⦄ & L1 ⊢ U1 ⬌* U2.
/3 width=3 by lsubsv_fwd_lsubss, lsubss_ssta_trans/
qed-.

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

(*
include "basic_2/computation/xprs_lsubss.ma".
*)
include "basic_2/equivalence/lsubse.ma".

(* LOCAL ENVIRONMENT REFINEMENT FOR CONTEXT-SENSITIVE PARALLEL EQUIVALENCE **)

(* Properties on stratified native type assignment **************************)

axiom lsubse_ssta_trans: ∀h,g,L2,T,U2,l. ⦃h, L2⦄ ⊢ T •[g,l] U2 →
                         ∀L1. h ⊢ L1 ⊢•⊑[g] L2 →
                         ∃∃U1. ⦃h, L1⦄ ⊢ T •[g,l] U1 & L1 ⊢ U1 ⬌* U2.

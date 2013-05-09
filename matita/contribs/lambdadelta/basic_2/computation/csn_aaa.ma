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

include "basic_2/computation/acp_aaa.ma".
include "basic_2/computation/csn_tstc_vector.ma".

(* CONTEXT-SENSITIVE STRONGLY NORMALIZING TERMS *****************************)

(* Main properties concerning atomic arity assignment ***********************)

theorem csn_aaa: ∀L,T,A. L ⊢ T ⁝ A → L ⊢ ⬊* T.
#L #T #A #H
@(acp_aaa … csn_acp csn_acr … H)
qed.

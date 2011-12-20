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

include "Basic_2/static/aaa.ma".
include "Basic_2/computation/csn_cr.ma".
include "Basic_2/computation/lsubcs.ma".

(* CONTEXT-SENSITIVE STRONGLY NORMALIZING TERMS *****************************)

(* Main propertis ***********************************************************)

axiom snc_aarity_csubcs: ∀L1,T,A. L1 ⊢ T ÷ A → ∀L2. L2 ⊑ L1 → {L2, T} ϵ 〚A〛.

lemma snc_aarity: ∀L,T,A. L ⊢ T ÷ A → {L, T} ϵ 〚A〛.
/2 width=3/ qed.

axiom csn_arity: ∀L,T,A. L ⊢ T ÷ A → L ⊢ ⇓ T.

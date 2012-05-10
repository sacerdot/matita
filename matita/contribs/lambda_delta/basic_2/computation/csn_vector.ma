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

include "basic_2/grammar/term_vector.ma".
include "basic_2/computation/csn.ma".

(* CONTEXT-SENSITIVE STRONGLY NORMALIZING TERM VECTORS **********************)

definition csnv: lenv → predicate (list term) ≝
                 λL. all … (csn L).

interpretation
   "context-sensitive strong normalization (term vector)"
   'SN L Ts = (csnv L Ts).

(* Basic inversion lemmas ***************************************************)

lemma csnv_inv_cons: ∀L,T,Ts. L ⊢ ⬇* T @ Ts → L ⊢ ⬇* T ∧ L ⊢ ⬇* Ts.
normalize // qed-.

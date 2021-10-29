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

include "ground/notation/functions/element_t_1.ma".
include "ground/relocation/pr_map.ma".
include "ground/arith/pnat.ma".

(* TOTAL RELOCATION MAPS ****************************************************)

definition tr_map: Type[0] ≝ stream pnat.

corec definition tr_inj: tr_map → pr_map.
* *
[ #f @(⫯(tr_inj f))
| #p #f @(↑(tr_inj (p⨮f)))
]
defined.

interpretation
  "injection (total relocation maps)"
  'ElementT f = (tr_inj f).

(* Basic constructions ******************************************************)

lemma tr_inj_unfold_unit (f): ⫯𝐭❨f❩ = 𝐭❨𝟏⨮f❩.
#f <(stream_unfold … (𝐭❨𝟏⨮f❩)) in ⊢ (???%); //
qed.

lemma tr_inj_unfold_succ (f): ∀p. ↑𝐭❨p⨮f❩ = 𝐭❨↑p⨮f❩.
#f #p <(stream_unfold … (𝐭❨↑p⨮f❩)) in ⊢ (???%); //
qed.

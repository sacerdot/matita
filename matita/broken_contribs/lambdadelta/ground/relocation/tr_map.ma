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

definition tr_map: Type[0] ≝ stream (ℕ⁺).

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

(* Basic inversions *********************************************************)

(*** push_inv_seq_sn *)
lemma eq_inv_cons_pr_push (f) (g):
      ∀p. 𝐭❨p⨮g❩ = ⫯f → ∧∧ 𝟏 = p & 𝐭❨g❩ = f.
#f #g *
[ <tr_inj_unfold_unit
  /3 width=1 by eq_inv_pr_push_bi, conj/
| #p <tr_inj_unfold_succ #H
  elim (eq_inv_pr_next_push … H)
]
qed-.

(*** push_inv_seq_dx *)
lemma eq_inv_pr_push_cons (f) (g):
      ∀p. ⫯f = 𝐭❨p⨮g❩ → ∧∧ 𝟏 = p & 𝐭❨g❩ = f.
#f #g *
[ <tr_inj_unfold_unit
  /3 width=1 by eq_inv_pr_push_bi, conj/
| #p <tr_inj_unfold_succ #H
  elim (eq_inv_pr_push_next … H)
]
qed-.

(*** next_inv_seq_sn *)
lemma eq_inv_cons_pr_next (f) (g):
      ∀p. 𝐭❨p⨮g❩ = ↑f → ∃∃q. 𝐭❨q⨮g❩ = f & ↑q = p.
#f #g *
[ <tr_inj_unfold_unit #H
  elim (eq_inv_pr_push_next … H)
| #p <tr_inj_unfold_succ #H
  /3 width=3 by eq_inv_pr_next_bi, ex2_intro/
]
qed-.

(*** next_inv_seq_dx *)
lemma eq_inv_pr_next_cons (f) (g):
      ∀p. ↑f = 𝐭❨p⨮g❩ → ∃∃q. 𝐭❨q⨮g❩ = f & ↑q = p.
#f #g *
[ <tr_inj_unfold_unit #H
  elim (eq_inv_pr_next_push … H)
| #p <tr_inj_unfold_succ #H
  /3 width=3 by eq_inv_pr_next_bi, ex2_intro/
]
qed-.

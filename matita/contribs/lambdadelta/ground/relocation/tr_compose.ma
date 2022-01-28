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

include "ground/lib/stream_tls.ma".
include "ground/relocation/tr_pap.ma".

(* COMPOSITION FOR TOTAL RELOCATION MAPS ************************************)

corec definition tr_compose: tr_map → tr_map → tr_map.
#f2 * #p1 #f1
@(stream_cons … (f2@❨p1❩))
@(tr_compose ? f1) -tr_compose -f1
@(⇂*[p1]f2)
defined.

interpretation
  "composition (total relocation maps)"
  'compose f2 f1 = (tr_compose f2 f1).

(* Basic constructions ******************************************************)

(*** compose_rew *)
lemma tr_compose_unfold (f2) (f1):
      ∀p1. f2@❨p1❩⨮(⇂*[p1]f2)∘f1 = f2∘(p1⨮f1).
#f2 #f1 #p1 <(stream_unfold … (f2∘(p1⨮f1))) //
qed.

(* Basic inversions *********************************************************)

(*** compose_inv_rew *)
lemma tr_compose_inv_unfold (f2) (f1):
      ∀f,p1,p. f2∘(p1⨮f1) = p⨮f →
      ∧∧ f2@❨p1❩ = p & (⇂*[p1]f2)∘f1 = f.
#f2 #f1 #f #p1 #p
<tr_compose_unfold #H destruct
/2 width=1 by conj/
qed-.

(*** compose_inv_S2 *)
lemma tr_compose_inv_succ_dx (f2) (f1):
      ∀f,p2,p1,p. (p2⨮f2)∘(↑p1⨮f1) = p⨮f →
      ∧∧ f2@❨p1❩+p2 = p & f2∘(p1⨮f1) = f2@❨p1❩⨮f.
#f2 #f1 #f #p2 #p1 #p
<tr_compose_unfold #H destruct
>nsucc_inj <stream_tls_swap
/2 width=1 by conj/
qed-.

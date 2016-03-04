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

include "ground_2/notation/functions/droppred_1.ma".
include "ground_2/relocation/rtmap_eq.ma".

(* RELOCATION MAP ***********************************************************)

definition tl: rtmap → rtmap.
@case_type0 #f @f
defined.

interpretation "tail (rtmap)" 'DropPred f = (tl f).

(* Basic properties *********************************************************)

lemma tl_rew: ∀f. case_type0 (λ_:rtmap.rtmap) (λf:rtmap.f) (λf:rtmap.f) f = ⫱f.
// qed.

lemma tl_push_rew: ∀f. f = ⫱↑f.
#f <tl_rew <iota_push //
qed.

lemma tl_next_rew: ∀f. f = ⫱⫯f.
#f <tl_rew <iota_next //
qed.

lemma tl_eq_repl: eq_repl … (λf1,f2. ⫱f1 ≗ ⫱f2).
#f1 #f2 * -f1 -f2 //
qed.

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

include "ground/notation/functions/downspoon_1.ma".
include "ground/lib/stream_hdtl.ma".
include "ground/relocation/p1/pr_map.ma".

(* TAIL FOR PARTIAL RELOCATION MAPS *****************************************)

(*** tl *)
definition pr_tl (f): pr_map ≝ ⇂f.

interpretation
  "tail (partial relocation maps)"
  'DownSpoon f = (pr_tl f).

(* Basic constructions ******************************************************)

(*** tl_push_rew *)
lemma pr_tl_push (f): f = ⫰⫯f.
// qed.

(*** tl_next_rew *)
lemma pr_tl_next (f): f = ⫰↑f.
// qed.

(* Basic eliminations *******************************************************)

(*** pn_split pr_map_split *)
lemma pr_map_split_tl (f): ∨∨ ⫯⫰f = f | ↑⫰f = f.
* * /2 width=1 by or_introl, or_intror/
qed-.

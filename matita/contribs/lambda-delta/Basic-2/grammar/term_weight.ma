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

include "Basic-2/grammar/term.ma".

(* WEIGHT *******************************************************************)

(* the weight of a term *)
let rec tw T ≝ match T with
[ TSort _     ⇒ 1
| TLRef _     ⇒ 1
| TPair _ V T ⇒ tw V + tw T + 1
].

interpretation "weight (term)" 'Weight T = (tw T).

axiom tw_wf_ind: ∀P:term→Prop.
                 (∀T2. (∀T1. # T1 < # T2 → P T1) → P T2) →
                 ∀T. P T.

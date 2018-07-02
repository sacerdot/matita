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

include "ground_2/notation/relations/ringeq_3.ma".
include "apps_2/notation/models/at_3.ma".
include "apps_2/notation/models/wbrackets_4.ma".
include "static_2/syntax/term.ma".

(* MODEL ********************************************************************)

record model: Type[1] ≝ {
   dd: Type[0];                            (* denotations domain *)
   sq: relation2 dd dd;                    (* structural equivalence *)
   sv: nat → dd;                           (* sort evaluation *)
   ap: dd → dd → dd;                       (* application *)
   ti: (nat → dd) → (nat → dd) → term → dd (* term interperpretation *)
}.

interpretation "structural equivalence (model)"
   'RingEq M d1 d2 = (sq M d1 d2).

interpretation "application (model)"
   'At M d1 d2 = (ap M d1 d2).

interpretation "term interpretation (model)"
   'WBrackets M gv lv T = (ti M gv lv T).

definition evaluation: model → Type[0] ≝ λM. nat → dd M.

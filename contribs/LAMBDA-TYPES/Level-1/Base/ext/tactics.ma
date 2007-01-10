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

(* This file was automatically generated: do not edit *********************)

set "baseuri" "cic:/matita/LAMBDA-TYPES/Level-1/Base/ext/tactics".

include "preamble.ma".

theorem insert_eq:
 \forall (S: Set).(\forall (x: S).(\forall (P: ((S \to Prop))).(\forall (G: 
Prop).(((\forall (y: S).((P y) \to ((eq S y x) \to G)))) \to ((P x) \to G)))))
\def
 \lambda (S: Set).(\lambda (x: S).(\lambda (P: ((S \to Prop))).(\lambda (G: 
Prop).(\lambda (H: ((\forall (y: S).((P y) \to ((eq S y x) \to 
G))))).(\lambda (H0: (P x)).(H x H0 (refl_equal S x))))))).

theorem unintro:
 \forall (A: Set).(\forall (a: A).(\forall (P: ((A \to Prop))).(((\forall (x: 
A).(P x))) \to (P a))))
\def
 \lambda (A: Set).(\lambda (a: A).(\lambda (P: ((A \to Prop))).(\lambda (H: 
((\forall (x: A).(P x)))).(H a)))).

theorem xinduction:
 \forall (A: Set).(\forall (t: A).(\forall (P: ((A \to Prop))).(((\forall (x: 
A).((eq A t x) \to (P x)))) \to (P t))))
\def
 \lambda (A: Set).(\lambda (t: A).(\lambda (P: ((A \to Prop))).(\lambda (H: 
((\forall (x: A).((eq A t x) \to (P x))))).(H t (refl_equal A t))))).


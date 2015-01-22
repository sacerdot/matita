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

include "Ground-1/preamble.ma".

theorem insert_eq:
 \forall (S: Set).(\forall (x: S).(\forall (P: ((S \to Prop))).(\forall (G: 
((S \to Prop))).(((\forall (y: S).((P y) \to ((eq S y x) \to (G y))))) \to 
((P x) \to (G x))))))
\def
 \lambda (S: Set).(\lambda (x: S).(\lambda (P: ((S \to Prop))).(\lambda (G: 
((S \to Prop))).(\lambda (H: ((\forall (y: S).((P y) \to ((eq S y x) \to (G 
y)))))).(\lambda (H0: (P x)).(H x H0 (refl_equal S x))))))).
(* COMMENTS
Initial nodes: 45
END *)

theorem unintro:
 \forall (A: Set).(\forall (a: A).(\forall (P: ((A \to Prop))).(((\forall (x: 
A).(P x))) \to (P a))))
\def
 \lambda (A: Set).(\lambda (a: A).(\lambda (P: ((A \to Prop))).(\lambda (H: 
((\forall (x: A).(P x)))).(H a)))).
(* COMMENTS
Initial nodes: 17
END *)

theorem xinduction:
 \forall (A: Set).(\forall (t: A).(\forall (P: ((A \to Prop))).(((\forall (x: 
A).((eq A t x) \to (P x)))) \to (P t))))
\def
 \lambda (A: Set).(\lambda (t: A).(\lambda (P: ((A \to Prop))).(\lambda (H: 
((\forall (x: A).((eq A t x) \to (P x))))).(H t (refl_equal A t))))).
(* COMMENTS
Initial nodes: 31
END *)


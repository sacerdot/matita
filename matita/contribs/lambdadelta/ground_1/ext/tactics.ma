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

include "ground_1/preamble.ma".

theorem insert_eq:
 \forall (S: Type[0]).(\forall (x: S).(\forall (P: ((S \to Prop))).(\forall 
(G: ((S \to Prop))).(((\forall (y: S).((P y) \to ((eq S y x) \to (G y))))) 
\to ((P x) \to (G x))))))
\def
 \lambda (S: Type[0]).(\lambda (x: S).(\lambda (P: ((S \to Prop))).(\lambda 
(G: ((S \to Prop))).(\lambda (H: ((\forall (y: S).((P y) \to ((eq S y x) \to 
(G y)))))).(\lambda (H0: (P x)).(let TMP_1 \def (refl_equal S x) in (H x H0 
TMP_1))))))).

theorem unintro:
 \forall (A: Type[0]).(\forall (a: A).(\forall (P: ((A \to Prop))).(((\forall 
(x: A).(P x))) \to (P a))))
\def
 \lambda (A: Type[0]).(\lambda (a: A).(\lambda (P: ((A \to Prop))).(\lambda 
(H: ((\forall (x: A).(P x)))).(H a)))).

theorem xinduction:
 \forall (A: Type[0]).(\forall (t: A).(\forall (P: ((A \to Prop))).(((\forall 
(x: A).((eq A t x) \to (P x)))) \to (P t))))
\def
 \lambda (A: Type[0]).(\lambda (t: A).(\lambda (P: ((A \to Prop))).(\lambda 
(H: ((\forall (x: A).((eq A t x) \to (P x))))).(let TMP_2 \def (refl_equal A 
t) in (H t TMP_2))))).


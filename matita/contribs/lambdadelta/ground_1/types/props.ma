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

include "ground_1/types/defs.ma".

theorem ex2_sym:
 \forall (A: Type[0]).(\forall (P: ((A \to Prop))).(\forall (Q: ((A \to 
Prop))).((ex2 A (\lambda (x: A).(P x)) (\lambda (x: A).(Q x))) \to (ex2 A 
(\lambda (x: A).(Q x)) (\lambda (x: A).(P x))))))
\def
 \lambda (A: Type[0]).(\lambda (P: ((A \to Prop))).(\lambda (Q: ((A \to 
Prop))).(\lambda (H: (ex2 A (\lambda (x: A).(P x)) (\lambda (x: A).(Q 
x)))).(let TMP_10 \def (\lambda (x: A).(P x)) in (let TMP_9 \def (\lambda (x: 
A).(Q x)) in (let TMP_7 \def (\lambda (x: A).(Q x)) in (let TMP_6 \def 
(\lambda (x: A).(P x)) in (let TMP_8 \def (ex2 A TMP_7 TMP_6) in (let TMP_5 
\def (\lambda (x: A).(\lambda (H0: (P x)).(\lambda (H1: (Q x)).(let TMP_4 
\def (\lambda (x0: A).(Q x0)) in (let TMP_3 \def (\lambda (x0: A).(P x0)) in 
(ex_intro2 A TMP_4 TMP_3 x H1 H0)))))) in (ex2_ind A TMP_10 TMP_9 TMP_8 TMP_5 
H)))))))))).


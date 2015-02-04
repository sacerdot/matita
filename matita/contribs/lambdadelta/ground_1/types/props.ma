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
x)))).(let TMP_1 \def (\lambda (x: A).(P x)) in (let TMP_2 \def (\lambda (x: 
A).(Q x)) in (let TMP_3 \def (\lambda (x: A).(Q x)) in (let TMP_4 \def 
(\lambda (x: A).(P x)) in (let TMP_5 \def (ex2 A TMP_3 TMP_4) in (let TMP_8 
\def (\lambda (x: A).(\lambda (H0: (P x)).(\lambda (H1: (Q x)).(let TMP_6 
\def (\lambda (x0: A).(Q x0)) in (let TMP_7 \def (\lambda (x0: A).(P x0)) in 
(ex_intro2 A TMP_6 TMP_7 x H1 H0)))))) in (ex2_ind A TMP_1 TMP_2 TMP_5 TMP_8 
H)))))))))).


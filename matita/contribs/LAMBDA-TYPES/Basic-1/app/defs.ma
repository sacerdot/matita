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

include "Basic-1/C/defs.ma".

definition cbk:
 C \to nat
\def
 let rec cbk (c: C) on c: nat \def (match c with [(CSort m) \Rightarrow m | 
(CHead c0 _ _) \Rightarrow (cbk c0)]) in cbk.

definition app1:
 C \to (T \to T)
\def
 let rec app1 (c: C) on c: (T \to T) \def (\lambda (t: T).(match c with 
[(CSort _) \Rightarrow t | (CHead c0 k u) \Rightarrow (app1 c0 (THead k u 
t))])) in app1.


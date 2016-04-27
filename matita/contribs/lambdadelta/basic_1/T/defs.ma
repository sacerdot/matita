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

include "basic_1/preamble.ma".

inductive B: Type[0] \def
| Abbr: B
| Abst: B
| Void: B.

inductive F: Type[0] \def
| Appl: F
| Cast: F.

inductive K: Type[0] \def
| Bind: B \to K
| Flat: F \to K.

inductive T: Type[0] \def
| TSort: nat \to T
| TLRef: nat \to T
| THead: K \to (T \to (T \to T)).

rec definition tweight (t: T) on t: nat \def match t with [(TSort _) 
\Rightarrow (S O) | (TLRef _) \Rightarrow (S O) | (THead _ u t0) \Rightarrow 
(S (plus (tweight u) (tweight t0)))].

definition tle:
 T \to (T \to Prop)
\def
 \lambda (t1: T).(\lambda (t2: T).(le (tweight t1) (tweight t2))).


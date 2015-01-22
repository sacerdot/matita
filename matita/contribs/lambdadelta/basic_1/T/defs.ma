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

include "Basic-1/preamble.ma".

inductive B: Set \def
| Abbr: B
| Abst: B
| Void: B.

inductive F: Set \def
| Appl: F
| Cast: F.

inductive K: Set \def
| Bind: B \to K
| Flat: F \to K.

inductive T: Set \def
| TSort: nat \to T
| TLRef: nat \to T
| THead: K \to (T \to (T \to T)).

definition tweight:
 T \to nat
\def
 let rec tweight (t: T) on t: nat \def (match t with [(TSort _) \Rightarrow 
(S O) | (TLRef _) \Rightarrow (S O) | (THead _ u t0) \Rightarrow (S (plus 
(tweight u) (tweight t0)))]) in tweight.


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

set "baseuri" "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta/T/defs".

include "preamble.ma".

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

inductive TList: Set \def
| TNil: TList
| TCons: T \to (TList \to TList).

definition THeads:
 K \to (TList \to (T \to T))
\def
 let rec THeads (k: K) (us: TList) on us: (T \to T) \def (\lambda (t: 
T).(match us with [TNil \Rightarrow t | (TCons u ul) \Rightarrow (THead k u 
(THeads k ul t))])) in THeads.

definition tweight:
 T \to nat
\def
 let rec tweight (t: T) on t: nat \def (match t with [(TSort _) \Rightarrow 
(S O) | (TLRef _) \Rightarrow (S O) | (THead _ u t0) \Rightarrow (S (plus 
(tweight u) (tweight t0)))]) in tweight.


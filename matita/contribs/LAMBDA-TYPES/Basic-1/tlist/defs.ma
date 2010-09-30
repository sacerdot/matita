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

include "Basic-1/T/defs.ma".

inductive TList: Set \def
| TNil: TList
| TCons: T \to (TList \to TList).

definition THeads:
 K \to (TList \to (T \to T))
\def
 let rec THeads (k: K) (us: TList) on us: (T \to T) \def (\lambda (t: 
T).(match us with [TNil \Rightarrow t | (TCons u ul) \Rightarrow (THead k u 
(THeads k ul t))])) in THeads.

definition TApp:
 TList \to (T \to TList)
\def
 let rec TApp (ts: TList) on ts: (T \to TList) \def (\lambda (v: T).(match ts 
with [TNil \Rightarrow (TCons v TNil) | (TCons t ts0) \Rightarrow (TCons t 
(TApp ts0 v))])) in TApp.

definition tslen:
 TList \to nat
\def
 let rec tslen (ts: TList) on ts: nat \def (match ts with [TNil \Rightarrow O 
| (TCons _ ts0) \Rightarrow (S (tslen ts0))]) in tslen.

definition tslt:
 TList \to (TList \to Prop)
\def
 \lambda (ts1: TList).(\lambda (ts2: TList).(lt (tslen ts1) (tslen ts2))).


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

include "basic_1/T/defs.ma".

inductive TList: Type[0] \def
| TNil: TList
| TCons: T \to (TList \to TList).

let rec THeads (k: K) (us: TList) on us: T \to T \def \lambda (t: T).(match 
us with [TNil \Rightarrow t | (TCons u ul) \Rightarrow (THead k u (THeads k 
ul t))]).

let rec TApp (ts: TList) on ts: T \to TList \def \lambda (v: T).(match ts 
with [TNil \Rightarrow (TCons v TNil) | (TCons t ts0) \Rightarrow (TCons t 
(TApp ts0 v))]).

let rec tslen (ts: TList) on ts: nat \def match ts with [TNil \Rightarrow O | 
(TCons _ ts0) \Rightarrow (S (tslen ts0))].

definition tslt:
 TList \to (TList \to Prop)
\def
 \lambda (ts1: TList).(\lambda (ts2: TList).(lt (tslen ts1) (tslen ts2))).


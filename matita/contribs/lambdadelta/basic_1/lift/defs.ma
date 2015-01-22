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

include "Basic-1/tlist/defs.ma".

include "Basic-1/s/defs.ma".

definition lref_map:
 ((nat \to nat)) \to (nat \to (T \to T))
\def
 let rec lref_map (f: ((nat \to nat))) (d: nat) (t: T) on t: T \def (match t 
with [(TSort n) \Rightarrow (TSort n) | (TLRef i) \Rightarrow (TLRef (match 
(blt i d) with [true \Rightarrow i | false \Rightarrow (f i)])) | (THead k u 
t0) \Rightarrow (THead k (lref_map f d u) (lref_map f (s k d) t0))]) in 
lref_map.

definition lift:
 nat \to (nat \to (T \to T))
\def
 \lambda (h: nat).(\lambda (i: nat).(\lambda (t: T).(lref_map (\lambda (x: 
nat).(plus x h)) i t))).

definition lifts:
 nat \to (nat \to (TList \to TList))
\def
 let rec lifts (h: nat) (d: nat) (ts: TList) on ts: TList \def (match ts with 
[TNil \Rightarrow TNil | (TCons t ts0) \Rightarrow (TCons (lift h d t) (lifts 
h d ts0))]) in lifts.


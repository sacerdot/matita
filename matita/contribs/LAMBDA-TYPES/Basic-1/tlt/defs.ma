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

definition wadd:
 ((nat \to nat)) \to (nat \to (nat \to nat))
\def
 \lambda (f: ((nat \to nat))).(\lambda (w: nat).(\lambda (n: nat).(match n 
with [O \Rightarrow w | (S m) \Rightarrow (f m)]))).

definition weight_map:
 ((nat \to nat)) \to (T \to nat)
\def
 let rec weight_map (f: ((nat \to nat))) (t: T) on t: nat \def (match t with 
[(TSort _) \Rightarrow O | (TLRef n) \Rightarrow (f n) | (THead k u t0) 
\Rightarrow (match k with [(Bind b) \Rightarrow (match b with [Abbr 
\Rightarrow (S (plus (weight_map f u) (weight_map (wadd f (S (weight_map f 
u))) t0))) | Abst \Rightarrow (S (plus (weight_map f u) (weight_map (wadd f 
O) t0))) | Void \Rightarrow (S (plus (weight_map f u) (weight_map (wadd f O) 
t0)))]) | (Flat _) \Rightarrow (S (plus (weight_map f u) (weight_map f 
t0)))])]) in weight_map.

definition weight:
 T \to nat
\def
 weight_map (\lambda (_: nat).O).

definition tlt:
 T \to (T \to Prop)
\def
 \lambda (t1: T).(\lambda (t2: T).(lt (weight t1) (weight t2))).


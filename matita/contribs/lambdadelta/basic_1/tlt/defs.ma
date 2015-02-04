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

definition wadd:
 ((nat \to nat)) \to (nat \to (nat \to nat))
\def
 \lambda (f: ((nat \to nat))).(\lambda (w: nat).(\lambda (n: nat).(match n 
with [O \Rightarrow w | (S m) \Rightarrow (f m)]))).

let rec weight_map (f: (nat \to nat)) (t: T) on t: nat \def match t with 
[(TSort _) \Rightarrow O | (TLRef n) \Rightarrow (f n) | (THead k u t0) 
\Rightarrow (match k with [(Bind b) \Rightarrow (match b with [Abbr 
\Rightarrow (let TMP_12 \def (weight_map f u) in (let TMP_13 \def (weight_map 
f u) in (let TMP_14 \def (S TMP_13) in (let TMP_15 \def (wadd f TMP_14) in 
(let TMP_16 \def (weight_map TMP_15 t0) in (let TMP_17 \def (plus TMP_12 
TMP_16) in (S TMP_17))))))) | Abst \Rightarrow (let TMP_8 \def (weight_map f 
u) in (let TMP_9 \def (wadd f O) in (let TMP_10 \def (weight_map TMP_9 t0) in 
(let TMP_11 \def (plus TMP_8 TMP_10) in (S TMP_11))))) | Void \Rightarrow 
(let TMP_4 \def (weight_map f u) in (let TMP_5 \def (wadd f O) in (let TMP_6 
\def (weight_map TMP_5 t0) in (let TMP_7 \def (plus TMP_4 TMP_6) in (S 
TMP_7)))))]) | (Flat _) \Rightarrow (let TMP_1 \def (weight_map f u) in (let 
TMP_2 \def (weight_map f t0) in (let TMP_3 \def (plus TMP_1 TMP_2) in (S 
TMP_3))))])].

definition weight:
 T \to nat
\def
 let TMP_1 \def (\lambda (_: nat).O) in (weight_map TMP_1).

definition tlt:
 T \to (T \to Prop)
\def
 \lambda (t1: T).(\lambda (t2: T).(let TMP_1 \def (weight t1) in (let TMP_2 
\def (weight t2) in (lt TMP_1 TMP_2)))).

definition tle:
 T \to (T \to Prop)
\def
 \lambda (t1: T).(\lambda (t2: T).(let TMP_1 \def (tweight t1) in (let TMP_2 
\def (tweight t2) in (le TMP_1 TMP_2)))).


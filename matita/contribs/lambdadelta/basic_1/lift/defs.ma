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

include "basic_1/tlist/defs.ma".

include "basic_1/s/defs.ma".

let rec lref_map (f: (nat \to nat)) (d: nat) (t: T) on t: T \def match t with 
[(TSort n) \Rightarrow (TSort n) | (TLRef i) \Rightarrow (let TMP_4 \def 
(match (blt i d) with [true \Rightarrow i | false \Rightarrow (f i)]) in 
(TLRef TMP_4)) | (THead k u t0) \Rightarrow (let TMP_1 \def (lref_map f d u) 
in (let TMP_2 \def (s k d) in (let TMP_3 \def (lref_map f TMP_2 t0) in (THead 
k TMP_1 TMP_3))))].

definition lift:
 nat \to (nat \to (T \to T))
\def
 \lambda (h: nat).(\lambda (i: nat).(\lambda (t: T).(let TMP_1 \def (\lambda 
(x: nat).(plus x h)) in (lref_map TMP_1 i t)))).

let rec lifts (h: nat) (d: nat) (ts: TList) on ts: TList \def match ts with 
[TNil \Rightarrow TNil | (TCons t ts0) \Rightarrow (let TMP_1 \def (lift h d 
t) in (let TMP_2 \def (lifts h d ts0) in (TCons TMP_1 TMP_2)))].


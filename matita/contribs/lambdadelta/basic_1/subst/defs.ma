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

include "basic_1/lift/defs.ma".

let rec subst (d: nat) (v: T) (t: T) on t: T \def match t with [(TSort n) 
\Rightarrow (TSort n) | (TLRef i) \Rightarrow (let TMP_4 \def (blt i d) in 
(match TMP_4 with [true \Rightarrow (TLRef i) | false \Rightarrow (let TMP_5 
\def (blt d i) in (match TMP_5 with [true \Rightarrow (let TMP_6 \def (pred 
i) in (TLRef TMP_6)) | false \Rightarrow (lift d O v)]))])) | (THead k u t0) 
\Rightarrow (let TMP_1 \def (subst d v u) in (let TMP_2 \def (s k d) in (let 
TMP_3 \def (subst TMP_2 v t0) in (THead k TMP_1 TMP_3))))].


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

include "Basic-1/lift/defs.ma".

definition subst:
 nat \to (T \to (T \to T))
\def
 let rec subst (d: nat) (v: T) (t: T) on t: T \def (match t with [(TSort n) 
\Rightarrow (TSort n) | (TLRef i) \Rightarrow (match (blt i d) with [true 
\Rightarrow (TLRef i) | false \Rightarrow (match (blt d i) with [true 
\Rightarrow (TLRef (pred i)) | false \Rightarrow (lift d O v)])]) | (THead k 
u t0) \Rightarrow (THead k (subst d v u) (subst (s k d) v t0))]) in subst.


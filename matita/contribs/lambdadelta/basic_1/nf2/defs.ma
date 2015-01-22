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

include "Basic-1/pr2/defs.ma".

definition nf2:
 C \to (T \to Prop)
\def
 \lambda (c: C).(\lambda (t1: T).(\forall (t2: T).((pr2 c t1 t2) \to (eq T t1 
t2)))).

definition nfs2:
 C \to (TList \to Prop)
\def
 let rec nfs2 (c: C) (ts: TList) on ts: Prop \def (match ts with [TNil 
\Rightarrow True | (TCons t ts0) \Rightarrow (land (nf2 c t) (nfs2 c ts0))]) 
in nfs2.


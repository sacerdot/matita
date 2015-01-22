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

include "Basic-1/drop/defs.ma".

include "Basic-1/lift1/defs.ma".

inductive drop1: PList \to (C \to (C \to Prop)) \def
| drop1_nil: \forall (c: C).(drop1 PNil c c)
| drop1_cons: \forall (c1: C).(\forall (c2: C).(\forall (h: nat).(\forall (d: 
nat).((drop h d c1 c2) \to (\forall (c3: C).(\forall (hds: PList).((drop1 hds 
c2 c3) \to (drop1 (PCons h d hds) c1 c3)))))))).

definition ptrans:
 PList \to (nat \to PList)
\def
 let rec ptrans (hds: PList) on hds: (nat \to PList) \def (\lambda (i: 
nat).(match hds with [PNil \Rightarrow PNil | (PCons h d hds0) \Rightarrow 
(let j \def (trans hds0 i) in (let q \def (ptrans hds0 i) in (match (blt j d) 
with [true \Rightarrow (PCons h (minus d (S j)) q) | false \Rightarrow 
q])))])) in ptrans.


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

inductive iso: T \to (T \to Prop) \def
| iso_sort: \forall (n1: nat).(\forall (n2: nat).(iso (TSort n1) (TSort n2)))
| iso_lref: \forall (i1: nat).(\forall (i2: nat).(iso (TLRef i1) (TLRef i2)))
| iso_head: \forall (v1: T).(\forall (v2: T).(\forall (t1: T).(\forall (t2: 
T).(\forall (k: K).(iso (THead k v1 t1) (THead k v2 t2)))))).


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

include "Basic-1/sty0/defs.ma".

inductive sty1 (g: G) (c: C) (t1: T): T \to Prop \def
| sty1_sty0: \forall (t2: T).((sty0 g c t1 t2) \to (sty1 g c t1 t2))
| sty1_sing: \forall (t: T).((sty1 g c t1 t) \to (\forall (t2: T).((sty0 g c 
t t2) \to (sty1 g c t1 t2)))).


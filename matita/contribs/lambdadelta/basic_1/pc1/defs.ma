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

include "basic_1/pr1/defs.ma".

definition pc1:
 T \to (T \to Prop)
\def
 \lambda (t1: T).(\lambda (t2: T).(let TMP_1 \def (\lambda (t: T).(pr1 t1 t)) 
in (let TMP_2 \def (\lambda (t: T).(pr1 t2 t)) in (ex2 T TMP_1 TMP_2)))).


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



include "logic/connectives.ma".

theorem stupid: 
  \forall a,b,c:Prop.
  (a \land c \lor b \land c) \to (c \land (b \lor a)).
  intros.decompose.split.assumption.right.assumption.
  split.assumption.left.assumption.qed.

definition MyFalse \def False.

theorem ex_falso_quodlibet: \forall (P:Prop). MyFalse \to P.
 intros. decompose.
qed.

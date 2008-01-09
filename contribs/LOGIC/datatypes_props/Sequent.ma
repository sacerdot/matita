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



include "datatypes_defs/Sequent.ma".

theorem linj_inj: \forall a,c. linj a = linj c \to a = c.
 intros; whd in H:(? ? % %); destruct; autobatch.
qed.

theorem rinj_inj: \forall b,d. rinj b = rinj d \to b = d.
 intros; whd in H:(? ? % %); destruct; autobatch.
qed.

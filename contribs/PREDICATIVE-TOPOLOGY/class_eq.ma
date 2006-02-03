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

set "baseuri" "cic:/matita/PREDICATIVE-TOPOLOGY/class_eq".

include "class_le.ma".

theorem ceq_cl: \forall C,c1,c2. ceq ? c1 c2 \to cin C c1 \land cin C c2.
intros; elim H; clear H.
lapply cle_cl to H1 using H; clear H1; decompose H;
lapply cle_cl to H2 using H; clear H2; decompose H.
auto.
qed.

theorem ceq_refl: \forall C,c. cin C c \to ceq ? c c.
intros; apply ceq_intro; auto.
qed.

theorem ceq_trans: \forall C,c2,c1,c3.
                   ceq C c2 c3 \to ceq ? c1 c2 \to ceq ? c1 c3.
intros; elim H; elim H1; clear H; clear H1.
apply ceq_intro; apply cle_trans; [|auto|auto||auto|auto].
qed.

theorem ceq_sym: \forall C,c1,c2. ceq C c1 c2 \to ceq C c2 c1.
intros; elim H; clear H.; auto.
qed.

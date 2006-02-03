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

set "baseuri" "cic:/matita/PREDICATIVE-TOPOLOGY/class_le".

include "class_defs.ma".

theorem cle_cl: \forall C,c1,c2. cle ? c1 c2 \to cin C c1 \land cin C c2.
intros; elim H; clear H; clear c2; 
   [| decompose H2 ]; auto.
qed.

theorem cle_trans: \forall C,c1,c2. cle C c1 c2 \to 
                   \forall c3. cle ? c3 c1 \to cle ? c3 c2.
intros 4; elim H; clear H; clear c2;
   [| apply ceq_sing; [||| apply H4 ]]; auto.
qed.

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



include "CLE/defs.ma".
include "Insert/inv.ma".

(* Functional properties ****************************************************)
(*
theorem insert_total: \forall S,i,P. i <= P \to \exists Q. Insert S i P Q.
 intros 4; elim H; clear H i P;
 decompose; autobatch.
qed.  

theorem insert_inj: \forall S1,i,P, Q. Insert S1 i P Q \to 
                    \forall S2. Insert S2 i P Q \to S1 = S2.
 intros 5; elim H; clear H i P Q;
 [ lapply linear insert_inv_zero to H1; destruct; autobatch
 | lapply linear insert_inv_succ to H3; decompose; destruct; autobatch
 ].
qed.
*)

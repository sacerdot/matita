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



(*
*)

include "Insert/fun.ma".
(*
theorem insert_conf: \forall P,Q1,S1,i1. Insert S1 i1 P Q1 \to 
                     \forall Q2,S2,i2. Insert S2 i2 P Q2 \to
                     \exists Q,j1,j2. 
                     Insert S2 j2 Q1 Q \land Insert S1 j1 Q2 Q.
 intros 5. elim H; clear H i1 P Q1;
 [ elim H1; clear H1 i2 c Q2; decompose; autobatch depth = 7 size = 8
 | lapply linear insert_inv_abst_1 to H3. decompose; destruct;
   [ autobatch depth = 7 size = 8
   | lapply linear H2 to H4. decompose. destruct. autobatch depth = 6 size = 8
   ]
 ].
qed. 

theorem insert_trans: \forall P1,Q1,S1,i1. Insert S1 i1 P1 Q1 \to 
                      \forall Q2,S2,i2. Insert S2 i2 Q1 Q2 \to
                      \exists P2,j1,j2. 
                      Insert S2 j2 P1 P2 \land Insert S1 j1 P2 Q2.
 intros 5. elim H; clear H i1 P1 Q1;
 [ lapply linear insert_inv_abst_1 to H1. decompose; destruct; autobatch depth = 6 size = 7
 | lapply linear insert_inv_abst_1 to H3. decompose; destruct;
   [ clear H2. autobatch depth = 7 size = 8
   | lapply linear H2 to H4. decompose. destruct. autobatch depth = 6 size = 8
   ]
 ].
qed.

theorem insert_conf_rev: \forall P1,Q,S1,i1. Insert S1 i1 P1 Q \to 
                         \forall P2,S2,i2. Insert S2 i2 P2 Q \to
                         (i1 = i2 \land P1 = P2) \lor 
                         \exists Q1,Q2,j1,j2. 
                         Insert S2 j2 Q2 P1 \land Insert S1 j1 Q1 P2.
 intros 5; elim H; clear H i1 P1 Q;
 [ inversion H1; clear H1; intros; destruct; autobatch depth = 7 size = 8
 | inversion H3; clear H3; intros; destruct;
   [ autobatch depth = 7 size = 8
   | clear H3; lapply linear H2 to H; decompose; destruct;
     autobatch depth = 8 size = 10
   ]
 ].
qed.

theorem insert_conf_rev_full: \forall P1,Q,S1,i1. Insert S1 i1 P1 Q \to 
                              \forall P2,S2,i2. Insert S2 i2 P2 Q \to
                              (S1 = S2 \land i1 = i2 \land P1 = P2) \lor 
                              \exists Q1,Q2,j1,j2. 
                              Insert S2 j2 Q2 P1 \land Insert S1 j1 Q1 P2.
 intros; lapply insert_conf_rev to H, H1; decompose; destruct;
 [ lapply linear insert_inj to H, H1; destruct; autobatch depth = 4
 | autobatch depth = 7 size = 8
 ].
qed.
*)

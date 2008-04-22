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



(**)

include "PEq/defs.ma".
include "PRed/defs.ma".
include "WLT/defs.ma".
(*
theorem pred_wlt: \forall p1,p2,Q1,Q2,S.
                  [Q1, p1, S] => [Q2, p2, S] \to \lnot [Q1, p1] = [Q2, p2] \to
                  [Q2, p2] < [Q1, p1].
 intros 6; elim H; clear H;
 [ unfold Not in H1; lapply linear depth = 1 H1;
   [ decompose | autobatch ]
*)

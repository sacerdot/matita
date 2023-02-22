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



include "Insert/fun.ma".
include "Track/defs.ma".

(* Order properties *********************************************************)
(*
theorem track_refl: \forall P. \forall c:Formula. \exists r. 
                    Track P r (pair c c).
 intros; elim c; clear c;
 [ autobatch
 | lapply (insert_total (pair f f1) zero P); [2:autobatch];
   decompose; autobatch depth = 5 width = 4 size = 8
 ].
qed.

theorem track_trans: \forall P,p,q,A,B. \forall c:Formula.
                     Track P p (pair A c) \to Track P q (pair c B) \to
                     \exists r. Track P r (pair A B).
 intros; autobatch.
qed.
*)

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

include "ground/arith/nat_tri.ma".
include "ground/arith/nat_succ.ma".

(* SUCCESSOR FOR NON-NEGATIVE INTEGERS **************************************)

(* Rewrites with ntri *******************************************************)

lemma ntri_succ_bi (A) (a1) (a2) (a3) (n1) (n2):
      ntri A (n1) (n2) a1 a2 a3 = ntri A (↑n1) (↑n2) a1 a2 a3.
#A #a1 #a2 #a3 * [| #p1 ] * //
qed.

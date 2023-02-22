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

(* Constructions with ntri **************************************************)

lemma ntri_zero_succ (A) (a1) (a2) (a3) (n):
      a1 = ntri A (𝟎) (↑n) a1 a2 a3.
#A #a1 #a2 #a3 * //
qed.

lemma ntri_succ_zero (A) (a1) (a2) (a3) (n):
      a3 = ntri A (↑n) (𝟎) a1 a2 a3.
#A #a1 #a2 #a3 * //
qed.

lemma ntri_succ_bi (A) (a1) (a2) (a3) (n1) (n2):
      ntri A (n1) (n2) a1 a2 a3 = ntri A (↑n1) (↑n2) a1 a2 a3.
#A #a1 #a2 #a3 * [| #p1 ] * //
qed.

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

include "ground/arith/nat_succ.ma".
include "ground/arith/int_succ.ma".
include "ground/arith/int_nat.ma".

(* NATURAL INTEGERS *********************************************************)

(* Constractions with nsucc *************************************************)

lemma znat_succ (n):
      ↑⊕n = ⊕(⁤↑n).
* //
qed.

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

include "ground/arith/nat_iter.ma".
include "ground/arith/nat_ppred.ma".

(* POSITIVE PREDECESSOR FOR NON-NEGATIVE INTEGERS ***************************)

(* Constructions with niter *************************************************)

lemma niter_pos_ppred (A) (f) (p):
      f∘f^(↓p) ⊜ f^❪A❫(⁤p).
#A #f * //
qed.

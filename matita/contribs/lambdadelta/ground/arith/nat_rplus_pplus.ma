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

include "ground/arith/pnat_plus.ma".
include "ground/arith/nat_rplus.ma".

(* RIGHT ADDITION FOR NON-NEGATIVE INTEGERS *********************************)

(* Constructions with pplus *************************************************)

lemma nrplus_inj_dx (p) (q):
      p + q = p + ninj q.
// qed.

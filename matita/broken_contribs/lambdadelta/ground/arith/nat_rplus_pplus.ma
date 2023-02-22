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
include "ground/arith/nat_pred.ma".
include "ground/arith/nat_rplus_succ.ma".

(* RIGHT ADDITION FOR NON-NEGATIVE INTEGERS *********************************)

(* Constructions with pplus *************************************************)

lemma nrplus_inj_dx (p) (q):
      p + q = p + ninj q.
// qed.

lemma nrplus_pnpred_dx (p) (q):
      pnpred (p+q) = nrplus p (pnpred q).
#p * //
qed.

lemma nrplus_pplus_assoc (p,q:pnat) (n:nat):
      (p+q)+n = p+(q+n).
#p #q #n
@(nat_ind_succ … n) -n // #n #IH
<nrplus_succ_dx <nrplus_succ_dx <pplus_succ_dx //
qed.

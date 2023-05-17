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

include "ground/arith/nat_rplus_pplus.ma".
include "ground/arith/nat_plus_rplus.ma".

(* ADDITION FOR NON-NEGATIVE INTEGERS ***************************************)

lemma nplus_inj_bi (p) (q):
      npos (pplus p q) = nplus (npos p) (npos q).
// qed.

lemma nplus_pnpred_sn (p) (q):
      pnpred (p + q) = nplus (pnpred p) (npos q).
#p #q
<pplus_comm >nplus_comm >nrplus_pnpred_dx //
qed.

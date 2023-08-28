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

lemma nplus_pos_bi (p) (q):
      (⁤(p+q)) = (⁤p)+(⁤q).
#p #q
>nrplus_pos_dx <nplus_pos_sn //
qed.

lemma nplus_pnpred_sn (p) (q):
      ↓(p+q) = (↓p) + (⁤q).
#p #q
<pplus_comm >nplus_comm >nrplus_pnpred_dx //
qed.

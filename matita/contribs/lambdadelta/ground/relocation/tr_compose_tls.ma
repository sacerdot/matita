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

include "ground/relocation/tr_compose.ma".
include "ground/lib/stream_tls_plus.ma".
include "ground/arith/nat_plus_rplus.ma".
include "ground/arith/nat_rplus_pplus.ma".

(* COMPOSITION FOR TOTAL RELOCATION MAPS ************************************)

(* Advanced constructions with stream_tls ***********************************)

lemma tr_compose_tls (i) (f2) (f1):
      (⇂*[f1@❨i❩]f2)∘⇂*[i]f1 = ⇂*[i](f2∘f1).
#i elim i -i
[ #f2 * #p1 #f1 //
| #i #IH #f2 * #p1 #f1
  >nsucc_inj <stream_tls_swap <stream_tls_swap
  <tr_pap_succ >nrplus_inj_dx >nrplus_inj_sn
  <tr_compose_unfold <IH -IH //
]
qed.

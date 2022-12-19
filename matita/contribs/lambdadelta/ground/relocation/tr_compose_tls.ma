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

lemma tr_compose_tls (p) (f1) (f2):
      (⇂*[f1＠⧣❨p❩]f2)∘(⇂*[p]f1) = ⇂*[p](f2∘f1).
#p elim p -p [| #p #IH ] * #q1 #f1 #f2 //
<tr_compose_unfold <tr_cons_pap_succ
>nsucc_inj <stream_tls_succ_lcons <stream_tls_succ_lcons
<IH -IH >nrplus_inj_dx >nrplus_inj_sn <stream_tls_plus //
qed.

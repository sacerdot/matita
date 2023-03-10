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

include "ground/lib/stream_tls.ma".
include "ground/arith/nat_pred_succ.ma".
include "ground/relocation/tr_pn_hdtl.ma".

(* PUSH AND NEXT FOR TOTAL RELOCATION MAPS **********************************)

(* Constructions with stream_tls ********************************************)

(*** tls_next *)
lemma tr_tls_next (f):
      ∀p:pnat. ⇂*[p]f = ⇂*[p]↑f.
#f #p
>(npsucc_pred p) <stream_tls_swap <stream_tls_swap //
qed.

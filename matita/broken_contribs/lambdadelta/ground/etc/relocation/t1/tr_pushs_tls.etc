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

include "ground/relocation/t1/tr_pushs.ma".
include "ground/relocation/t1/tr_pn_hdtl.ma".
include "ground/lib/stream_tls.ma".

(* ITERATED PUSH FOR TOTAL RELOCATION MAPS **********************************)

(* Constructions with stream_tls ********************************************)

lemma tr_tls_pushs (f) (n):
      f = ⇂*[n]⫯*[n]f.
#f #n @(nat_ind_succ … n) -n //
#n #IH
<stream_tls_swap <tr_pushs_succ <tr_tl_push //
qed.

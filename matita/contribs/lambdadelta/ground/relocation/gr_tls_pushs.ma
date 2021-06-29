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

include "ground/relocation/gr_pushs.ma".
include "ground/relocation/gr_tls.ma".

(* ITERATED TAIL FOR GENERIC RELOCATION MAPS ********************************)

(* Constructions with gr_pushs **********************************************)

(*** tls_pushs *)
lemma gr_tls_pushs (n) (f): f = ⫰*[n] ⫯*[n] f.
#n @(nat_ind_succ … n) -n //
#n #IH #f <gr_tls_swap <gr_pushs_succ <gr_tl_push //
qed.

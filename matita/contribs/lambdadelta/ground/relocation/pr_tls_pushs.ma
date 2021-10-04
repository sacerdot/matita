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

include "ground/relocation/pr_pushs.ma".
include "ground/relocation/pr_tls.ma".

(* ITERATED TAIL FOR PARTIAL RELOCATION MAPS ********************************)

(* Constructions with pr_pushs **********************************************)

(*** tls_pushs *)
lemma pr_tls_pushs (n) (f): f = ⫰*[n] ⫯*[n] f.
#n @(nat_ind_succ … n) -n //
#n #IH #f <pr_tls_swap <pr_pushs_succ <pr_tl_push //
qed.

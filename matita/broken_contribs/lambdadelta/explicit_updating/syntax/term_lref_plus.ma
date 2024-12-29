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

include "ground/arith/nat_rplus_succ.ma".
include "explicit_updating/syntax/term_lref.ma".

(* VARIABLE REFERENCE BY DEPTH FOR TERM *************************************)

(* Constructions with nat_rplus *********************************************)

lemma term_lref_plus (p) (n):
      ↑*[n]𝛏❨p❩ = 𝛏❨p+n❩.
#p #n @(nat_ind_succ … n) -n // #n #IH
<term_nexts_succ <nrplus_succ_dx <term_lref_succ //
qed.

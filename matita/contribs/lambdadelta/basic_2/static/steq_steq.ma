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

include "basic_2/static/steq.ma".

(* STRATIFIED EQUIVALENCE FOR TERMS *****************************************)

(* Main properties **********************************************************)

theorem steq_trans: ∀h,g. Transitive … (steq h g).
#h #g #T1 #T * //
#k1 #k #Hk1 #HK2 #X #H elim (steq_inv … H) -H /2 width=1 by steq_zero/
* /2 width=1 by steq_zero/
qed-.

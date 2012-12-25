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

include "basic_2/unfold/csups.ma".
include "basic_2/computation/yprs.ma".

(* HYPER PARALLEL COMPUTATION ON CLOSURES ***********************************)

(* Properties on iterated supclosure ****************************************)

lemma csups_yprs: ∀h,g,L1,L2,T1,T2. ⦃L1, T1⦄ >* ⦃L2, T2⦄ →
                  h ⊢ ⦃L1, T1⦄ •⥸*[g] ⦃L2, T2⦄.
#h #g #L1 #L2 #T1 #T2 #H @(csups_ind … H) -L2 -T2 /3 width=1/ /3 width=4/
qed.

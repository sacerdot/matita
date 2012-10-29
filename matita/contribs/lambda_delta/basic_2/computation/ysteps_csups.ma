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

include "basic_2/computation/yprs_csups.ma".
include "basic_2/computation/ysteps.ma".

(* ITERATED STEP OF HYPER PARALLEL COMPUTATION ON CLOSURES ******************)

(* Properties on iterated supclosure ****************************************)

lemma csups_ysteps: ∀h,g,L1,L2,T1,T2. ⦃L1, T1⦄ >* ⦃L2, T2⦄ →
                    h ⊢ ⦃L1, T1⦄ •⭃*[g] ⦃L2, T2⦄.
#h #g #L1 #L2 #T1 #T2 #H
lapply (csups_fwd_cw … H) #H1
@ysteps_intro /2 width=1/ -H #H2 #H3 destruct
elim (lt_refl_false … H1)
qed.

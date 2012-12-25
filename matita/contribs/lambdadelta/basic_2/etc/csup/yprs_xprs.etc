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

include "basic_2/computation/xprs_cprs.ma".
include "basic_2/computation/yprs.ma".

(* HYPER PARALLEL COMPUTATION ON CLOSURES ***********************************)

(* Properties on extended parallel computation for terms ********************)

lemma xprs_yprs: ∀h,g,L,T1,T2. ⦃h, L⦄ ⊢ T1 •➡*[g] T2 →
                 h ⊢ ⦃L, T1⦄ •⥸*[g] ⦃L, T2⦄.
#h #g #L #T1 #T2 #H @(xprs_ind … H) -T2 // /3 width=4/
qed.

lemma cprs_yprs: ∀h,g,L,T1,T2. L ⊢ T1 ➡* T2 → h ⊢ ⦃L, T1⦄ •⥸*[g] ⦃L, T2⦄.
/3 width=1/ qed.

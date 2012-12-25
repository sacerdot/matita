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

include "basic_2/computation/cprs.ma".
include "basic_2/computation/xprs.ma".

(* EXTENDED PARALLEL COMPUTATION ON TERMS ***********************************)

(* properties on context sensitive parallel computation for terms ***********)

lemma cprs_xprs: ∀h,g,L,T1,T2. L ⊢ T1 ➡* T2 → ⦃h, L⦄ ⊢ T1 •➡*[g] T2.
#h #g #L #T1 #T2 #H @(cprs_ind … H) -T2 // /3 width=3/
qed.

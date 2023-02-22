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

include "basic_2/i_dynamic/ntas_preserve.ma".

(* ITERATED NATIVE TYPE ASSIGNMENT FOR TERMS ********************************)

(* Main properties **********************************************************)

theorem ntas_trans (h) (a) (G) (L) (T0):
        ∀n1,T1. ❨G,L❩ ⊢ T1 :*[h,a,n1] T0 →
        ∀n2,T2. ❨G,L❩ ⊢ T0 :*[h,a,n2] T2 → ❨G,L❩ ⊢ T1 :*[h,a,n1+n2] T2.
#h #a #G #L #T0 #n1 #T1 * #X1 #HT0 #HT1 #H01 #H11 #n2 #T2 * #X2 #HT2 #_ #H22 #H02
elim (cnv_cpms_conf … HT0 … H01 … H02) -T0 <minus_O_n <minus_n_O #X0 #H10 #H20
/3 width=5 by ntas_intro, cpms_trans/
qed-.

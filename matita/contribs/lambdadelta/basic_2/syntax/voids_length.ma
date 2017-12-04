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

include "basic_2/syntax/lenv_length.ma".
include "basic_2/syntax/voids.ma".

(* EQUIVALENCE FOR LOCAL ENVIRONMENTS UP TO EXCLUSION BINDERS ***************)

(* Forward lemmas with length for local environments ************************)

lemma voids_fwd_length_le_sn: ∀L1,L2,n1,n2. ⓧ*[n1]L1 ≋ ⓧ*[n2]L2 → n1 ≤ |L1|.
#L1 #L2 #n1 #n2 #H elim H -L1 -L2 -n1 -n2 normalize
/2 width=1 by le_S_S/
qed-.

lemma voids_fwd_length_le_dx: ∀L1,L2,n1,n2. ⓧ*[n1]L1 ≋ ⓧ*[n2]L2 → n2 ≤ |L2|.
#L1 #L2 #n1 #n2 #H elim H -L1 -L2 -n1 -n2 normalize
/2 width=1 by le_S_S/
qed-.

lemma voids_fwd_length: ∀L1,L2,n1,n2. ⓧ*[n1]L1 ≋ ⓧ*[n2]L2 →
                        |L1| + n2 = |L2| + n1.
#L1 #L2 #n1 #n2 #H elim H -L1 -L2 -n1 -n2 normalize
/2 width=2 by injective_plus_r/
qed-.

lemma voids_fwd_length_minus: ∀L1,L2,n1,n2. ⓧ*[n1]L1 ≋ ⓧ*[n2]L2 →
                              |L1| - n1 = |L2| - n2.
/3 width=3 by voids_fwd_length, voids_fwd_length_le_dx, voids_fwd_length_le_sn, plus_to_minus_2/ qed-.

lemma voids_inj_length: ∀L1,L2,n1,n2. ⓧ*[n1]L1 ≋ ⓧ*[n2]L2 →
                        |L1| = |L2| → n1 = n2.
#L1 #L2 #n1 #n2 #H #HL12
lapply (voids_fwd_length … H) -H #H
/2 width=2 by injective_plus_l/
qed-.

(* Inversion lemmas with length for local environments **********************)

lemma voids_inv_void_dx_length: ∀L1,L2,n1,n2. ⓧ*[n1]L1 ≋ ⓧ*[n2]L2.ⓧ → |L1| ≤ |L2| →
                                ∃∃m2. ⓧ*[n1]L1 ≋ ⓧ*[m2]L2 & n2 = ⫯m2 & n1 ≤ m2.
#L1 #L2 #n1 #n2 #H #HL12
lapply (voids_fwd_length … H) normalize >plus_n_Sm #H0
lapply (plus2_inv_le_sn … H0 HL12) -H0 -HL12 #H0
elim (le_inv_S1 … H0) -H0 #m2 #Hm2 #H0 destruct
/3 width=4 by voids_inv_void_dx, ex3_intro/
qed-.

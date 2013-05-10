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

include "basic_2/unfold/delift_lift.ma".
include "basic_2/unfold/delift_delift.ma".
include "basic_2/computation/cprs_delift.ma".
include "basic_2/equivalence/cpcs_cpcs.ma".

(* CONTEXT-SENSITIVE PARALLEL EQUIVALENCE ON TERMS **************************)

(* Properties on inverse basic term relocation ******************************)

lemma cpcs_zeta_delift_comm: ∀L,V,T1,T2. L.ⓓV ⊢ ▼*[O, 1] T1 ≡ T2 →
                             L ⊢ T2 ⬌* +ⓓV.T1.
/3 width=1/ qed.

(* Basic_1: was only: pc3_gen_cabbr *)
lemma thin_cpcs_delift_mono: ∀L,U1,U2. L ⊢ U1 ⬌* U2 →
                             ∀K,d,e. ▼*[d, e] L ≡ K → ∀T1. L ⊢ ▼*[d, e] U1 ≡ T1 →
                             ∀T2. L ⊢ ▼*[d, e] U2 ≡ T2 → K ⊢ T1 ⬌* T2.
#L #U1 #U2 #H #K #d #e #HLK #T1 #HTU1 #T2 #HTU2
elim (cpcs_inv_cprs … H) -H #U #HU1 #HU2
elim (thin_cprs_delift_conf … HU1 … HLK … HTU1) -U1 #T #HT1 #HUT
elim (thin_cprs_delift_conf … HU2 … HLK … HTU2) -U2 -HLK #X #HT2 #H
lapply (delift_mono … H … HUT) -L #H destruct /2 width=3/
qed.

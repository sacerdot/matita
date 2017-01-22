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

include "basic_2/reducibility/cpr_delift.ma".
include "basic_2/reducibility/cpr_cpr.ma".
include "basic_2/computation/cprs.ma".

(* CONTEXT-SENSITIVE PARALLEL COMPUTATION ON TERMS **************************)

(* Properties on inverse basic term relocation ******************************)

(* Note: this should be stated with tprs *)
lemma cprs_zeta_delift: ∀L,V,T1,T2. L.ⓓV ⊢ ▼*[O, 1] T1 ≡ T2 → L ⊢ +ⓓV.T1 ➡* T2.
#L #V #T1 #T2 * #T #HT1 #HT2
@(cprs_strap2 … (+ⓓV.T)) [ /3 width=3/ | @inj /3 width=3/ ] (**) (* explicit constructor, /5 width=3/ is too slow *)
qed.

(* Basic_1: was only: pr3_gen_cabbr *)
lemma thin_cprs_delift_conf: ∀L,U1,U2. L ⊢ U1 ➡* U2 →
                             ∀K,d,e. ▼*[d, e] L ≡ K → ∀T1. L ⊢ ▼*[d, e] U1 ≡ T1 →
                             ∃∃T2. K ⊢ T1 ➡* T2 & L ⊢ ▼*[d, e] U2 ≡ T2.
#L #U1 #U2 #H @(cprs_ind … H) -U2 /2 width=3/
#U #U2 #_ #HU2 #IHU1 #K #d #e #HLK #T1 #HTU1
elim (IHU1 … HLK … HTU1) -U1 #T #HT1 #HUT
elim (thin_cpr_delift_conf … HU2 … HLK … HUT) -U -HLK /3 width=3/
qed.

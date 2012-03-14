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

include "basic_2/reducibility/cpr.ma".

(* CONTEXT-SENSITIVE PARALLEL COMPUTATION ON TERMS **************************)

(* Basic_1: includes: pr3_pr2 *)
definition cprs: lenv → relation term ≝
                 λL. TC … (cpr L).

interpretation "context-sensitive parallel computation (term)"
   'PRedStar L T1 T2 = (cprs L T1 T2).

(* Basic eliminators ********************************************************)

lemma cprs_ind: ∀L,T1. ∀R:predicate term. R T1 →
                (∀T,T2. L ⊢ T1 ➡* T → L ⊢ T ➡ T2 → R T → R T2) →
                ∀T2. L ⊢ T1 ➡* T2 → R T2.
#L #T1 #R #HT1 #IHT1 #T2 #HT12 @(TC_star_ind … HT1 IHT1 … HT12) //
qed-.

axiom cprs_ind_dx: ∀L,T2. ∀R:predicate term. R T2 →
                   (∀T1,T. L ⊢ T1 ➡ T → L ⊢ T ➡* T2 → R T → R T1) →
                   ∀T1. L ⊢ T1 ➡* T2 → R T1.

(* Basic properties *********************************************************)

(* Basic_1: was: pr3_refl *)
lemma cprs_refl: ∀L,T. L ⊢ T ➡* T.
/2 width=1/ qed.

lemma cprs_strap1: ∀L,T1,T,T2.
                   L ⊢ T1 ➡* T → L ⊢ T ➡ T2 → L ⊢ T1 ➡* T2.
/2 width=3/ qed.

(* Basic_1: was: pr3_step *)
lemma cprs_strap2: ∀L,T1,T,T2.
                   L ⊢ T1 ➡ T → L ⊢ T ➡* T2 → L ⊢ T1 ➡* T2.
/2 width=3/ qed.

(* Note: it does not hold replacing |L1| with |L2| *)
lemma cprs_lsubs_conf: ∀L1,T1,T2. L1 ⊢ T1 ➡* T2 →
                       ∀L2. L1 [0, |L1|] ≼ L2 → L2 ⊢ T1 ➡* T2.
/3 width=3/
qed.

lemma cprs_flat_dx: ∀I,L,V1,V2. L ⊢ V1 ➡ V2 → ∀T1,T2. L ⊢ T1 ➡* T2 →
                    L ⊢ ⓕ{I} V1. T1 ➡* ⓕ{I} V2. T2.
#I #L #V1 #V2 #HV12 #T1 #T2 #HT12 @(cprs_ind … HT12) -T2 /3 width=1/
#T #T2 #_ #HT2 #IHT2
@(cprs_strap1 … IHT2) -IHT2 /2 width=1/
qed.

(* Basic inversion lemmas ***************************************************)

(* Basic_1: was: pr3_gen_sort *)
lemma cprs_inv_sort1: ∀L,U2,k. L ⊢ ⋆k ➡* U2 → U2 = ⋆k.
#L #U2 #k #H @(cprs_ind … H) -U2 //
#U2 #U #_ #HU2 #IHU2 destruct
>(cpr_inv_sort1 … HU2) -HU2 //
qed-.

(* Basic_1: was: pr3_gen_cast *)
lemma cprs_inv_cast1: ∀L,W1,T1,U2. L ⊢ ⓣW1.T1 ➡* U2 → L ⊢ T1 ➡* U2 ∨
                      ∃∃W2,T2. L ⊢ W1 ➡* W2 & L ⊢ T1 ➡* T2 & U2 = ⓣW2.T2.
#L #W1 #T1 #U2 #H @(cprs_ind … H) -U2 /3 width=5/
#U2 #U #_ #HU2 * /3 width=3/ *
#W #T #HW1 #HT1 #H destruct
elim (cpr_inv_cast1 … HU2) -HU2 /3 width=3/ *
#W2 #T2 #HW2 #HT2 #H destruct /4 width=5/
qed-.

(* Basic_1: removed theorems 6:
   clear_pr3_trans pr3_cflat pr3_gen_bind
   pr3_iso_appl_bind pr3_iso_appls_appl_bind pr3_iso_appls_bind
*)

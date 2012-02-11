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

include "Basic_2/reducibility/cpr.ma".

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

(* Basic_1: removed theorems 2: clear_pr3_trans pr3_cflat *)

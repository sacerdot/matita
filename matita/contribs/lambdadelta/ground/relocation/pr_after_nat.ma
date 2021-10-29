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

include "ground/relocation/pr_nat.ma".
include "ground/relocation/pr_after_pat.ma".

(* RELATIONAL COMPOSITION FOR PARTIAL RELOCATION MAPS ***********************)

(* Destructions with pr_nat *************************************************)

lemma pr_after_nat_des (l) (l1):
      ∀f. @↑❨l1, f❩ ≘ l → ∀f2,f1. f2 ⊚ f1 ≘ f →
      ∃∃l2. @↑❨l1, f1❩ ≘ l2 & @↑❨l2, f2❩ ≘ l.
#l #l1 #f #H1 #f2 #f1 #Hf
elim (pr_after_pat_des … H1 … Hf) -f #i2 #H1 #H2
/2 width=3 by ex2_intro/
qed-.

lemma pr_after_des_nat (l) (l2) (l1):
      ∀f1,f2. @↑❨l1, f1❩ ≘ l2 → @↑❨l2, f2❩ ≘ l →
      ∀f. f2 ⊚ f1 ≘ f → @↑❨l1, f❩ ≘ l.
/2 width=6 by pr_after_des_pat/ qed-.

lemma pr_after_des_nat_sn (l1) (l):
      ∀f. @↑❨l1, f❩ ≘ l → ∀f1,l2. @↑❨l1, f1❩ ≘ l2 →
      ∀f2. f2 ⊚ f1 ≘ f → @↑❨l2, f2❩ ≘ l.
/2 width=6 by pr_after_des_pat_sn/ qed-.

lemma pr_after_des_nat_dx (l) (l2) (l1):
      ∀f,f2. @↑❨l1, f❩ ≘ l → @↑❨l2, f2❩ ≘ l →
      ∀f1. f2 ⊚ f1 ≘ f → @↑❨l1, f1❩ ≘ l2.
/2 width=6 by pr_after_des_pat_dx/ qed-.

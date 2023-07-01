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

include "ground/relocation/p1/pr_eq.ma".
include "ground/relocation/p1/pr_tl.ma".

(* TAIL FOR PARTIAL RELOCATION MAPS *****************************************)

(* Constructions with pr_eq *************************************************)

(*** eq_refl *)
corec lemma pr_eq_refl: reflexive … pr_eq.
#f cases (pr_map_split_tl f) #Hf
[ @(pr_eq_push … Hf Hf) | @(pr_eq_next … Hf Hf) ] -Hf //
qed.

(*** tl_eq_repl *)
lemma pr_tl_eq_repl:
      pr_eq_repl … (λf1,f2. ⫰f1 ≐ ⫰f2).
#f1 #f2 * -f1 -f2 //
qed.

(* Inversions with pr_eq ****************************************************)

(*** eq_inv_gen *)
lemma pr_eq_inv_gen (g1) (g2):
      g1 ≐ g2 →
      ∨∨ ∧∧ ⫰g1 ≐ ⫰g2 & ⫯⫰g1 = g1 & ⫯⫰g2 = g2
       | ∧∧ ⫰g1 ≐ ⫰g2 & ↑⫰g1 = g1 & ↑⫰g2 = g2.
#g1 #g2 * -g1 -g2 #f1 #f2 #g1 #g2 #f * *
/3 width=1 by and3_intro, or_introl, or_intror/
qed-.

(* Advanced inversions with pr_eq *******************************************)

(*** pr_eq_inv_px *)
lemma pr_eq_inv_push_sn (g1) (g2):
      g1 ≐ g2 → ∀f1. ⫯f1 = g1 →
      ∧∧ f1 ≐ ⫰g2 & ⫯⫰g2 = g2.
#g1 #g2 #H #f1 #Hf1
elim (pr_eq_inv_gen … H) -H * #Hg #Hg1 #Hg2 destruct
[ /2 width=1 by conj/
| elim (eq_inv_pr_next_push … Hg1)
]
qed-.

(*** pr_eq_inv_nx *)
lemma pr_eq_inv_next_sn (g1) (g2):
      g1 ≐ g2 → ∀f1. ↑f1 = g1 →
      ∧∧ f1 ≐ ⫰g2 & ↑⫰g2 = g2.
#g1 #g2 #H #f1 #Hf1
elim (pr_eq_inv_gen … H) -H * #Hg #Hg1 #Hg2 destruct
[ elim (eq_inv_pr_push_next … Hg1)
| /2 width=1 by conj/
]
qed-.

(*** pr_eq_inv_xp *)
lemma pr_eq_inv_push_dx (g1) (g2):
      g1 ≐ g2 → ∀f2. ⫯f2 = g2 →
      ∧∧ ⫰g1 ≐ f2 & ⫯⫰g1 = g1.
#g1 #g2 #H #f2 #Hf2
elim (pr_eq_inv_gen … H) -H * #Hg #Hg1 #Hg2 destruct
[ /2 width=1 by conj/
| elim (eq_inv_pr_next_push … Hg2)
]
qed-.

(*** pr_eq_inv_xn *)
lemma pr_eq_inv_next_dx (g1) (g2):
      g1 ≐ g2 → ∀f2. ↑f2 = g2 →
      ∧∧ ⫰g1 ≐ f2 & ↑⫰g1 = g1.
#g1 #g2 #H #f2 #Hf2
elim (pr_eq_inv_gen … H) -H * #Hg #Hg1 #Hg2 destruct
[ elim (eq_inv_pr_push_next … Hg2)
| /2 width=1 by conj/
]
qed-.

(*** pr_eq_inv_pp *)
lemma pr_eq_inv_push_bi (g1) (g2):
      g1 ≐ g2 → ∀f1,f2. ⫯f1 = g1 → ⫯f2 = g2 → f1 ≐ f2.
#g1 #g2 #H #f1 #f2 #H1
elim (pr_eq_inv_push_sn … H … H1) -g1 #Hx2 * #H
lapply (eq_inv_pr_push_bi … H) -H //
qed-.

(*** pr_eq_inv_nn *)
lemma pr_eq_inv_next_bi (g1) (g2):
      g1 ≐ g2 → ∀f1,f2. ↑f1 = g1 → ↑f2 = g2 → f1 ≐ f2.
#g1 #g2 #H #f1 #f2 #H1
elim (pr_eq_inv_next_sn … H … H1) -g1 #Hx2 * #H
lapply (eq_inv_pr_next_bi … H) -H //
qed-.

(*** pr_eq_inv_pn *)
lemma pr_eq_inv_push_next (g1) (g2):
      g1 ≐ g2 → ∀f1,f2. ⫯f1 = g1 → ↑f2 = g2 → ⊥.
#g1 #g2 #H #f1 #f2 #H1
elim (pr_eq_inv_push_sn … H … H1) -g1 #Hx2 * #H
elim (eq_inv_pr_next_push … H)
qed-.

(*** pr_eq_inv_np *)
lemma pr_eq_inv_next_push (g1) (g2):
      g1 ≐ g2 → ∀f1,f2. ↑f1 = g1 → ⫯f2 = g2 → ⊥.
#g1 #g2 #H #f1 #f2 #H1
elim (pr_eq_inv_next_sn … H … H1) -g1 #Hx2 * #H
elim (eq_inv_pr_push_next … H)
qed-.

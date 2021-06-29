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

include "ground/relocation/gr_eq.ma".
include "ground/relocation/gr_tl.ma".

(* TAIL FOR GENERIC RELOCATION MAPS *****************************************)

(* Constructions with gr_eq *************************************************)

(*** eq_refl *)
corec lemma gr_eq_refl: reflexive … gr_eq.
#f cases (gr_map_split_tl f) #Hf
[ @(gr_eq_push … Hf Hf) | @(gr_eq_next … Hf Hf) ] -Hf //
qed.

(*** tl_eq_repl *)
lemma gr_tl_eq_repl:
      gr_eq_repl … (λf1,f2. ⫰f1 ≡ ⫰f2).
#f1 #f2 * -f1 -f2 //
qed.

(* Inversions with gr_eq ****************************************************)

(*** eq_inv_gen *)
lemma gr_eq_inv_gen (g1) (g2):
      g1 ≡ g2 →
      ∨∨ ∧∧ ⫰g1 ≡ ⫰g2 & ⫯⫰g1 = g1 & ⫯⫰g2 = g2
       | ∧∧ ⫰g1 ≡ ⫰g2 & ↑⫰g1 = g1 & ↑⫰g2 = g2.
#g1 #g2 * -g1 -g2 #f1 #f2 #g1 #g2 #f * *
/3 width=1 by and3_intro, or_introl, or_intror/
qed-.

(* Advanced inversions with gr_eq *******************************************)

(*** gr_eq_inv_px *)
lemma gr_eq_inv_push_sn (g1) (g2):
      g1 ≡ g2 → ∀f1. ⫯f1 = g1 →
      ∧∧ f1 ≡ ⫰g2 & ⫯⫰g2 = g2.
#g1 #g2 #H #f1 #Hf1
elim (gr_eq_inv_gen … H) -H * #Hg #Hg1 #Hg2 destruct
[ /2 width=1 by conj/
| elim (eq_inv_gr_next_push … Hg1)
]
qed-.

(*** gr_eq_inv_nx *)
lemma gr_eq_inv_next_sn (g1) (g2):
      g1 ≡ g2 → ∀f1. ↑f1 = g1 →
      ∧∧ f1 ≡ ⫰g2 & ↑⫰g2 = g2.
#g1 #g2 #H #f1 #Hf1
elim (gr_eq_inv_gen … H) -H * #Hg #Hg1 #Hg2 destruct
[ elim (eq_inv_gr_push_next … Hg1)
| /2 width=1 by conj/
]
qed-.

(*** gr_eq_inv_xp *)
lemma gr_eq_inv_push_dx (g1) (g2):
      g1 ≡ g2 → ∀f2. ⫯f2 = g2 →
      ∧∧ ⫰g1 ≡ f2 & ⫯⫰g1 = g1.
#g1 #g2 #H #f2 #Hf2
elim (gr_eq_inv_gen … H) -H * #Hg #Hg1 #Hg2 destruct
[ /2 width=1 by conj/
| elim (eq_inv_gr_next_push … Hg2)
]
qed-.

(*** gr_eq_inv_xn *)
lemma gr_eq_inv_next_dx (g1) (g2):
      g1 ≡ g2 → ∀f2. ↑f2 = g2 →
      ∧∧ ⫰g1 ≡ f2 & ↑⫰g1 = g1.
#g1 #g2 #H #f2 #Hf2
elim (gr_eq_inv_gen … H) -H * #Hg #Hg1 #Hg2 destruct
[ elim (eq_inv_gr_push_next … Hg2)
| /2 width=1 by conj/
]
qed-.

(*** gr_eq_inv_pp *)
lemma gr_eq_inv_push_bi (g1) (g2):
      g1 ≡ g2 → ∀f1,f2. ⫯f1 = g1 → ⫯f2 = g2 → f1 ≡ f2.
#g1 #g2 #H #f1 #f2 #H1
elim (gr_eq_inv_push_sn … H … H1) -g1 #Hx2 * #H
lapply (eq_inv_gr_push_bi … H) -H //
qed-.

(*** gr_eq_inv_nn *)
lemma gr_eq_inv_next_bi (g1) (g2):
      g1 ≡ g2 → ∀f1,f2. ↑f1 = g1 → ↑f2 = g2 → f1 ≡ f2.
#g1 #g2 #H #f1 #f2 #H1
elim (gr_eq_inv_next_sn … H … H1) -g1 #Hx2 * #H
lapply (eq_inv_gr_next_bi … H) -H //
qed-.

(*** gr_eq_inv_pn *)
lemma gr_eq_inv_push_next (g1) (g2):
      g1 ≡ g2 → ∀f1,f2. ⫯f1 = g1 → ↑f2 = g2 → ⊥.
#g1 #g2 #H #f1 #f2 #H1
elim (gr_eq_inv_push_sn … H … H1) -g1 #Hx2 * #H
elim (eq_inv_gr_next_push … H)
qed-.

(*** gr_eq_inv_np *)
lemma gr_eq_inv_next_push (g1) (g2):
      g1 ≡ g2 → ∀f1,f2. ↑f1 = g1 → ⫯f2 = g2 → ⊥.
#g1 #g2 #H #f1 #f2 #H1
elim (gr_eq_inv_next_sn … H … H1) -g1 #Hx2 * #H
elim (eq_inv_gr_push_next … H)
qed-.

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

include "ground/notation/relations/rfun_c_2.ma".
include "ground/arith/nat_succ.ma".
include "ground/relocation/pr_isi.ma".

(* FINITE COLENGTH ASSIGNMENT FOR PARTIAL RELOCATION MAPS *******************)

(*** fcla *)
inductive pr_fcla: relation2 pr_map (ℕ) ≝
(*** fcla_isid *)
| pr_fcla_isi (f): 𝐈❨f❩ → pr_fcla f (𝟎)
(*** fcla_push *)
| pr_fcla_push (f) (n): pr_fcla f n → pr_fcla (⫯f) n
(*** fcla_next *)
| pr_fcla_next (f) (n): pr_fcla f n → pr_fcla (↑f) (↑n)
.

interpretation
  "finite colength assignment (partial relocation maps)"
  'RFunC f n = (pr_fcla f n).

(* Basic inversions *********************************************************)

(*** fcla_inv_px *)
lemma pr_fcla_inv_push (g) (m):
      (𝐂❨g❩ ≘ m) → ∀f. ⫯f = g → 𝐂❨f❩ ≘ m.
#g #m * -g -m
[ /3 width=3 by pr_fcla_isi, pr_isi_inv_push/
| #g #m #Hg #f #H >(eq_inv_pr_push_bi … H) -f //
| #g #m #_ #f #H elim (eq_inv_pr_push_next … H)
]
qed-.

(*** fcla_inv_nx *)
lemma pr_fcla_inv_next (g) (m):
         (𝐂❨g❩ ≘ m) → ∀f. ↑f = g →
         ∃∃n. 𝐂❨f❩ ≘ n & ↑n ={ℕ} m.
#g #m * -g -m
[ #g #Hg #f #H destruct
  elim (pr_isi_inv_next … Hg) -Hg //
| #g #m #_ #f #H elim (eq_inv_pr_next_push … H)
| #g #m #Hg #f #H >(eq_inv_pr_next_bi …  H) -f
  /2 width=3 by ex2_intro/
]
qed-.

(* Advanced inversions ******************************************************)

(*** cla_inv_nn *)
lemma pr_cla_inv_next_succ (g) (m):
      (𝐂❨g❩ ≘ m) → ∀f.∀n:ℕ. ↑f = g → ↑n ={ℕ} m → 𝐂❨f❩ ≘ n.
#g #m #H #f #n #H1 #H2 elim (pr_fcla_inv_next … H … H1) -g
#x #Hf #H destruct <(eq_inv_nsucc_bi … H) -n //
qed-.

(*** cla_inv_np *)
lemma pr_cla_inv_next_zero (g) (m):
      (𝐂❨g❩ ≘ m) → ∀f. ↑f = g → 𝟎 = m → ⊥.
#g #m #H #f #H1 elim (pr_fcla_inv_next … H … H1) -g
#x #_ #H1 #H2 destruct
qed-.

(*** fcla_inv_xp *)
lemma pr_fcla_inv_zero (g) (m):
      (𝐂❨g❩ ≘ m) → 𝟎 = m → 𝐈❨g❩.
#g #m #H elim H -g -m /3 width=3 by pr_isi_push/
#g #m #_ #_ #H destruct elim (eq_inv_zero_nsucc … H)
qed-.

(*** fcla_inv_isid *)
lemma pr_fcla_inv_isi (g) (m):
      (𝐂❨g❩ ≘ m) → 𝐈❨g❩ → 𝟎 = m.
#f #n #H elim H -f -n /3 width=3 by pr_isi_inv_push/
#f #n #_ #_ #H elim (pr_isi_inv_next … H) -H //
qed-.

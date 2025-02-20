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

(**) (* reverse include *)
include "ground/subsets/subset_and_eq.ma".
include "ground/subsets/subset_and_ext.ma".
include "ground/subsets/subset_ext_eq.ma".
include "delayed_updating/syntax/prototerm_eq.ma".
include "delayed_updating/substitution/lift_path_eq.ma".
include "delayed_updating/substitution/lift_prototerm.ma".

(* LIFT FOR PROTOTERM *******************************************************)

(* Constructions with subset_le *********************************************)

lemma lift_term_le_repl_dx (f):
      compatible_2_fwd … (subset_le …) (subset_le …) (λt.🠡[f]t).
/2 width=3 by subset_le_ext_f1_bi/
qed.

lemma lift_term_id_sn (t):
      t ⊆ 🠡[𝐢]t.
#t #p #Hp
>(lift_path_id p)
/2 width=1 by in_comp_lift_bi/
qed-.

lemma lift_term_id_dx (t):
      (🠡[𝐢]t) ⊆ t.
#t #p * #q #Hq #H destruct //
qed-.

lemma lift_term_grafted_sn (f) (t) (p):
      (🠡[🠢[p]f]⋔[p]t) ⊆ ⋔[🠡[f]p]🠡[f]t.
#f #t #p #q * #r #Hr #H0 destruct
/2 width=3 by ex2_intro/
qed-.

lemma lift_term_grafted_dx (f) (t) (p):
      (⋔[🠡[f]p]🠡[f]t) ⊆ 🠡[🠢[p]f]⋔[p]t.
#f #t #p #q * #r #Hr #H0
elim (eq_inv_lift_path_append … H0) -H0
#p0 #q0 #Hp0 #Hq0 #H0 destruct
lapply (lift_path_inj … Hp0) -Hp0 #Hp0 destruct
/2 width=1 by in_comp_lift_bi/
qed-.

lemma lift_pt_append_sn (f) (p) (u):
      (🠡[f]p)●(🠡[🠢[p]f]u) ⊆ 🠡[f](p●u).
#f #p #u #r * #q * #s #Hs #H1 #H2 destruct
>lift_path_append
/3 width=1 by in_comp_lift_bi, pt_append_in, subset_in_le_trans/
qed-.

lemma lift_pt_append_dx (f) (p) (u):
      (🠡[f](p●u)) ⊆ (🠡[f]p)●(🠡[🠢[p]f]u).
#f #p #u #r * #q * #s #Hs #H1 #H2 destruct
<lift_path_append
/3 width=1 by in_comp_lift_bi, pt_append_in, subset_in_le_trans/
qed-.

(* Constructions with subset_eq *********************************************)

lemma lift_term_eq_repl_sn (t):
      compatible_2_fwd … fbr_eq (subset_eq …) (λf.🠡[f]t).
/3 width=1 by subset_eq_ext_f1_exteq, lift_path_eq_repl/
qed.

lemma lift_term_eq_repl_dx (f):
      compatible_2_fwd … (subset_eq …) (subset_eq …) (λt.🠡[f]t).
/2 width=1 by subset_eq_ext_f1_bi/
qed.

lemma lift_term_and (f) (t1) (t2):
      (🠡[f]t1) ∩ (🠡[f]t2) ⇔ 🠡[f](t1 ∩ t2).
/3 width=2 by subset_and_ext_f1, lift_path_inj/
qed.

lemma lift_term_id (t):
      t ⇔ 🠡[𝐢]t.
/3 width=2 by lift_term_id_dx, lift_term_id_sn, conj/
qed.

lemma lift_term_grafted (f) (t) (p):
      (🠡[🠢[p]f]⋔[p]t) ⇔ ⋔[🠡[f]p]🠡[f]t.
/3 width=1 by lift_term_grafted_sn, lift_term_grafted_dx, conj/ qed.

lemma lift_term_grafted_S (f) (t) (p):
      (🠡[🠢[p]f]⋔[p◖𝗦]t) ⇔ ⋔[(🠡[f]p)◖𝗦](🠡[f]t).
// qed.

lemma lift_pt_append (f) (p) (u):
      (🠡[f]p)●(🠡[🠢[p]f]u) ⇔ 🠡[f](p●u).
/3 width=1 by conj, lift_pt_append_sn, lift_pt_append_dx/
qed.

lemma lift_slice_and_sn (f) (t) (p):
      (🠡[f]t)∩↑🠡[f]p ⇔ (🠡[f]t)∩🠡[f]↑p.
#f #t #p
@subset_eq_trans
[3: @(subset_and_eq_repl … (lift_pt_append …)) [| @subset_eq_refl ] | skip ]
@conj
[ @subset_le_and_dx //
  #r * * #s1 #Hs1 #H1 * #s2 #_ #H2 destruct >H2
  elim (eq_inv_append_lift_path … (sym_eq … H2)) -H2
  #r1 #r2 #H1 #H2 #_ -s1 destruct
  <(lift_path_inj … H1) -r1
  /3 width=1 by pt_append_in, in_comp_lift_bi/
| @subset_le_and_dx //
  @subset_le_trans [| @subset_le_and_sn_refl_dx ]
  /2 width=3 by pt_append_le_repl/
]
qed-.

lemma lift_and_slice_dx (f) (t) (p):
      (🠡[f]t)∩↑🠡[f]p ⇔ 🠡[f](t∩↑p).
#f #t #p
@(subset_eq_trans … (lift_slice_and_sn …)) //
qed.

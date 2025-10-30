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

include "delayed_updating/substitution/fsubst.ma".
include "delayed_updating/syntax/prototerm_ol.ma".
include "ground/subsets/subset_or_le.ma".
include "ground/subsets/subset_or_ol.ma".
include "ground/subsets/subset_and_ol.ma".

(* FOCALIZED SUBSTITUTION ***************************************************)

(* Constructions with subset_le *********************************************)

lemma fsubst_le_repl (t1) (t2) (u1) (u2) (v1) (v2):
      t1 ⊆ t2 → u1 ⇔ u2 → v1 ⊆ v2 → ⬕[u1←v1]t1 ⊆ ⬕[u2←v2]t2.
#t1 #t2 #u1 #u2 #v1 #v2 #Ht * #H1u #H2u #Hv #r * * #H1 #H2
/4 width=5 by subset_ol_le_repl, fsubst_in_comp_false, fsubst_in_comp_true/
qed.

lemma fsubst_le_true (t) (u) (v):
      t ≬ u → v ⊆ ⬕[u←v]t.
/2 width=1 by fsubst_in_comp_true/
qed.

lemma fsubst_le_false (t) (u) (v):
      t ⧵ u ⊆ ⬕[u←v]t.
#t #u #v #r * #Hr #Hnr
/2 width=1 by fsubst_in_comp_false/
qed.

lemma fsubst_le_or_sx_dx (t) (u) (v):
      ⬕[u←v]t ⊆ t ∪ v.
#t #u #v #p * *
/2 width=1 by subset_or_in_dx, subset_or_in_sx/
qed.

lemma fsubst_le_dx (t) (u) (v):
      t ≬ u → v ∪ (t ⧵ u) ⊆ ⬕[u←v]t.
/3 width=5 by fsubst_le_true, subset_le_or_sx, fsubst_le_false/
qed.

lemma fsubst_le_sx (t) (u) (v):
      t ≬ u → ⬕[u←v]t ⊆ v ∪ (t ⧵ u).
#t #u #v #Hu #r * *
/3 width=1 by subset_or_in_dx, subset_or_in_sx, conj/
qed.

lemma fsubst_and_rc_sx_sx (t) (u) (v):
      ⬕[t∩u←v]t ⊆ ⬕[u←v]t.
#t #u #v #r * *
[ /3 width=1 by fsubst_in_comp_true, subset_ol_inv_and_dx_refl_sx/
| /4 width=1 by fsubst_in_comp_false, subset_and_in/
]
qed-.

lemma fsubst_and_rc_sx_dx (t) (u) (v):
      ⬕[u←v]t ⊆ ⬕[t∩u←v]t.
#t #u #v #r * *
[ /3 width=1 by subset_ol_and_dx_refl_sx, fsubst_in_comp_true/
| #H1r #H0
  @fsubst_in_comp_false // -H1r
  * /2 width=1 by/
]
qed-.

lemma grafted_fsubst_false_dx (t) (u) (v) (p):
      p ⧸ϵ ▵u → ⋔[p]t ⊆ ⋔[p]⬕[u←v]t.
#t #u #v #p #Hnp #r #Hr
lapply (term_grafted_inv_gen … Hr) -Hr #Hpr
@term_grafted_gen
@fsubst_in_comp_false // -Hpr
/3 width=2 by term_in_root/
qed-.

lemma grafted_fsubst_false_sx (t) (u) (v) (p):
      p ⧸ϵ ▵v → ⋔[p]⬕[u←v]t ⊆ ⋔[p]t.
#t #u #v #p #Hnp #r #Hr
elim (term_grafted_inv_gen … Hr) -Hr *
[ #_ #Hpr elim Hnp -Hnp
  /2 width=2 by term_in_root/
| #Hpr #_ -Hnp
  /2 width=1 by term_grafted_gen/
]
qed-.

lemma grafted_fsubst_true_dx (t) (u) (v) (p):
      ⬕[⋔[p]u←⋔[p]v]⋔[p]t ⊆ ⋔[p]⬕[u←v]t.
#t #u #v #p #r * *
[ /4 width=2 by fsubst_in_comp_true, term_ol_des_grafted_bi, term_grafted_gen/
| /4 width=1 by fsubst_in_comp_false, term_grafted_gen/
]
qed-.

lemma grafted_fsubst_true_sx (t) (u) (v) (p):
      (⋔[p]t) ≬ ⋔[p]u → ⋔[p]⬕[u←v]t ⊆ ⬕[⋔[p]u←⋔[p]v]⋔[p]t.
#t #u #v #p #Hp #r #Hr
elim (term_grafted_inv_gen … Hr) -Hr *
[ /2 width=1 by fsubst_in_comp_true/
| /3 width=1 by fsubst_in_comp_false/
]
qed-.

lemma fsubst_le_repl_slice (t) (u1) (u2) (p1) (p2):
      t ⊆ u1 →
      ⬕[p1●u1←u2](p1●t) ⊆ ⬕[p2●u1←u2](p2●t).
#t #u1 #u2 #p1 #p2 #Ht #r * * #Hp #Hr
[ lapply (term_ol_inv_append_bi … Hp) -Hp #Hp
  /3 width=1 by fsubst_in_comp_true, term_ol_append_bi/
| @fsubst_in_comp_false
  elim Hr -Hr
  /2 width=3 by pt_append_le_repl/
]
qed.

(* Constructions with subset_eq *********************************************)

lemma fsubst_eq_repl (t1) (t2) (u1) (u2) (v1) (v2):
      t1 ⇔ t2 → u1 ⇔ u2 → v1 ⇔ v2 → ⬕[u1←v1]t1 ⇔ ⬕[u2←v2]t2.
#t1 #t2 #u1 #u2 #v1 #v2 * #H1t #H2t #Hu * #H1v #H2v
/4 width=7 by conj, fsubst_le_repl, subset_eq_sym/
qed.

lemma fsubst_or (t1) (t2) (u) (v):
      (⬕[u←v]t1) ∪ (⬕[u←v]t2) ⇔ ⬕[u←v](t1 ∪ t2).
#t1 #t2 #u #v @conj
[ @subset_le_or_sx @fsubst_le_repl // (**) (* auto fails *)
| #r * * [ #H0 | * ]
  [ elim (subset_ol_inv_or_sx … H0) -H0 #H0 #Hu
    /3 width=1 by fsubst_in_comp_true, subset_or_in_dx, subset_or_in_sx/
  | /3 width=1 by fsubst_in_comp_false, subset_or_in_sx/
  | /3 width=1 by fsubst_in_comp_false, subset_or_in_dx/
  ]
]
qed.

lemma fsubst_eq (t) (u) (v):
      t ≬ u → v ∪ (t ⧵ u) ⇔ ⬕[u←v]t.
/3 width=1 by fsubst_le_sx, fsubst_le_dx, conj/
qed.

lemma fsubst_and_rc_sx (t) (u) (v):
      ⬕[t∩u←v]t ⇔ ⬕[u←v]t.
/3 width=1 by conj, fsubst_and_rc_sx_sx, fsubst_and_rc_sx_dx/
qed.

lemma grafted_fsubst_false (t) (u) (v) (p):
      p ⧸ϵ ▵u → p ⧸ϵ ▵v →
      (⋔[p]t) ⇔ ⋔[p]⬕[u←v]t.
/3 width=4 by grafted_fsubst_false_sx, grafted_fsubst_false_dx, conj/
qed.

lemma grafted_fsubst_true (t) (u) (v) (p):
      (⋔[p]t) ≬ ⋔[p]u →
      ⬕[⋔[p]u←⋔[p]v]⋔[p]t ⇔ ⋔[p]⬕[u←v]t.
/3 width=4 by grafted_fsubst_true_sx, grafted_fsubst_true_dx, conj/
qed.

lemma fsubst_eq_repl_slice (t) (u1) (u2) (p1) (p2):
      t ⊆ u1 →
      ⬕[p1●u1←u2](p1●t) ⇔ ⬕[p2●u1←u2](p2●t).
/3 width=2 by conj, fsubst_le_repl_slice/
qed.

lemma fsubst_append (t) (u) (v) (p):
      p●(⬕[u←v]t) ⇔ ⬕[p●u←p●v](p●t).
#t #u #v #p @conj #r * [| * | * ]
[ #s * * #H1 #H2 #H3 destruct
  [ /3 width=1 by fsubst_in_comp_true, term_ol_append_bi, pt_append_in/
  | /4 width=2 by fsubst_in_comp_false, append_in_comp_inv_bi, pt_append_in/
  ]
| #H0 #Hr
  /4 width=3 by fsubst_in_comp_true, term_ol_inv_append_bi, pt_append_le_repl/
| * #s #Hs #H1 #H0 destruct
  /5 width=1 by fsubst_in_comp_false, append_in_comp_inv_bi, pt_append_in/
]
qed.

lemma fsubst_lcons_neq (t) (u) (v) (l1) (l2):
      l1 ⧸= l2 → l1◗t ⇔ ⬕[l2◗u←v](l1◗t).
#t #u #v #l1 #l2 #Hl @conj #r *
[ #s #Hs #H1 destruct
  @fsubst_in_comp_false
  [ /2 width=1 by pt_append_in/
  | * #r #_ #H0
    elim (eq_inv_list_rcons_bi ????? H0) -H0 #_
    /2 width=1 by/
  ]
| * #H0 #_ elim Hl -Hl -v -r
  /2 width=3 by term_ol_des_lcons_bi/
| * #Hr #_ -u -v -l2 //
]
qed.

(* Main inversions with subset_eq *******************************************)

theorem fsubst_2_inv_eq (t0) (t1) (t2) (t3) (t4)
          (u1) (u2) (v1) (v2) (x1) (x2) (y1) (y2):
        ⬕[u1←v1]⬕[u2←v2]t0 ⇔ ⬕[u2←v2]⬕[u1←v1]t0 →
        u1 ⇔ x1 → u2 ⇔ x2 → v1 ⇔ y1 → v2 ⇔ y2 →
        ⬕[u2←v2]t0 ⇔ t1 → ⬕[u1←v1]t0 ⇔ t2 →
        ⬕[x1←y1]t1 ⇔ t3 → ⬕[x2←y2]t2 ⇔ t4 →
        t3 ⇔ t4.
#t0 #t1 #t2 #t3 #t4 #u1 #u2 #v1 #v2 #x1 #x2 #y1 #y2
#Ht0 #Hux1 #Hux2 #Hvy1 #Hvy2 #Ht1 #Ht2 #Ht3 #Ht4
@(subset_eq_repl … Ht3 … Ht4) -t3 -t4
@(subset_eq_repl … Ht0) -Ht0
/2 width=1 by fsubst_eq_repl/
qed-.

theorem fsubst_3_inv_eq (t0) (t1) (t2) (t3) (t4) (t5)
          (u1) (u2) (u3) (v1) (v2) (v3) (x1) (x2) (x3) (y1) (y2) (y3):
        ⬕[u1←⬕[u3←v3]v1]⬕[u2←v2]t0 ⇔ ⬕[u3←v3]⬕[u2←v2]⬕[u1←v1]t0 →
        u1 ⇔ x1 → u2 ⇔ x2 → u3 ⇔ x3 →
        ⬕[x3←y3] v1 ⇔ y1 → v2 ⇔ y2 → v3 ⇔ y3 →
        ⬕[u2←v2]t0 ⇔ t1 → ⬕[u1←v1]t0 ⇔ t2 →
        ⬕[x1←y1]t1 ⇔ t3 → ⬕[x2←y2]t2 ⇔ t4 →
        ⬕[u3←v3]t4 ⇔ t5 →
        t3 ⇔ t5.
#t0 #t1 #t2 #t3 #t4 #t5 #u1 #u2 #u3 #v1 #v2 #v3 #x1 #x2 #x3 #y1 #y2 #y3
#Ht0 #Hux1 #Hux2 #Hux3 #Hvy1 #Hvy2 #Hvy3 #Ht01 #Ht02 #Ht13 #Ht24 #Ht45
@(subset_eq_repl … Ht13 … Ht45) -t3 -t5
lapply (subset_eq_trans … (fsubst_eq_repl … Hux3 Hvy3) … Hvy1)
[2: @subset_eq_refl | skip ] -x3 -y3 #Hvy1
@(subset_eq_canc_sx … (fsubst_eq_repl … Ht01 Hux1 Hvy1)) -x1 -y1 -t1
@(subset_eq_trans … Ht0) -Ht0
@fsubst_eq_repl [2,3: @subset_eq_refl ] -u3 -v3
@(subset_eq_trans … Ht24) -t4
@(fsubst_eq_repl … Ht02 Hux2 Hvy2)
qed-.

(* Constructions with subset_ol *********************************************)

lemma subset_ol_fsubst_sx (t) (u1) (u2) (v1):
      t ≬ u1 → v1 ≬ u2 → ⬕[u1←v1]t ≬ u2.
#t #u1 #u2 #v1 #Hu1 #Hv1
@(subset_ol_eq_repl … (fsubst_eq … Hu1) … (subset_eq_refl …)) -Hu1
/2 width=1 by subset_ol_or_sx_sx/
qed.

(* Inversions with subset_ol ************************************************)

lemma subset_ol_inv_fsubst_sx (t) (u1) (u2) (v1):
      t ≬ u1 → (t ⧵ u1) ⧸≬ u2 →
      ⬕[u1←v1]t ≬ u2 → v1 ≬ u2.
#t #u1 #u2 #v1 #Hu1 #Hu21 #H0
lapply (subset_ol_eq_repl … H0 … (subset_eq_sym …) … (subset_eq_refl …)) -H0
[ @fsubst_eq // | skip ] -Hu1 #H0
/2 width=3 by subset_ol_inv_or_sx_nol_dx/
qed-.

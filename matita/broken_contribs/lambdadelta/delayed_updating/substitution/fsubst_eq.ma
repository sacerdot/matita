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

lemma fsubst_le_or_sn_dx (t) (u) (v):
      ⬕[u←v]t ⊆ t ∪ v.
#t #u #v #p * *
/2 width=1 by subset_or_in_dx, subset_or_in_sn/
qed.

lemma fsubst_le_dx (t) (u) (v):
      t ≬ u → v ∪ (t ⧵ u) ⊆ ⬕[u←v]t.
/3 width=5 by fsubst_le_true, subset_le_or_sn, fsubst_le_false/
qed.

lemma fsubst_le_sn (t) (u) (v):
      t ≬ u → ⬕[u←v]t ⊆ v ∪ (t ⧵ u).
#t #u #v #Hu #r * *
/3 width=1 by subset_or_in_dx, subset_or_in_sn, conj/
qed.

lemma fsubst_and_rc_sn_sn (t) (u) (v):
      ⬕[t∩u←v]t ⊆ ⬕[u←v]t.
#t #u #v #r * *
[ /3 width=1 by fsubst_in_comp_true, subset_ol_inv_and_dx_refl_sn/
| /4 width=1 by fsubst_in_comp_false, subset_and_in/
]
qed-.

lemma fsubst_and_rc_sn_dx (t) (u) (v):
      ⬕[u←v]t ⊆ ⬕[t∩u←v]t.
#t #u #v #r * *
[ /3 width=1 by subset_ol_and_dx_refl_sn, fsubst_in_comp_true/
| #H1r #H0
  @fsubst_in_comp_false // -H1r
  * /2 width=1 by/
]
qed-.

lemma grafted_fsubst_dx (t) (u) (v) (p):
      p ⧸ϵ ▵u → ⋔[p]t ⊆ ⋔[p]⬕[u←v]t.
#t #u #v #p #Hnp #r #Hr
lapply (term_grafted_inv_gen … Hr) -Hr #Hpr
@term_grafted_gen
@fsubst_in_comp_false // -Hpr
/3 width=2 by term_in_root/
qed-.

lemma grafted_fsubst_sn (t) (u) (v) (p):
      p ⧸ϵ ▵v → ⋔[p]⬕[u←v]t ⊆ ⋔[p]t.
#t #u #v #p #Hnp #r #Hr
elim (term_grafted_inv_gen … Hr) -Hr *
[ #_ #Hpr elim Hnp -Hnp
  /2 width=2 by term_in_root/
| #Hpr #_ -Hnp
  /2 width=1 by term_grafted_gen/
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
[ @subset_le_or_sn @fsubst_le_repl // (**) (* auto fails *)
| #r * * [ #H0 | * ]
  [ elim (subset_ol_or_inv_sn … H0) -H0 #H0 #Hu
    /3 width=1 by fsubst_in_comp_true, subset_or_in_dx, subset_or_in_sn/
  | /3 width=1 by fsubst_in_comp_false, subset_or_in_sn/
  | /3 width=1 by fsubst_in_comp_false, subset_or_in_dx/
  ]
]
qed.

lemma fsubst_eq (t) (u) (v):
      t ≬ u → v ∪ (t ⧵ u) ⇔ ⬕[u←v]t.
/3 width=1 by fsubst_le_sn, fsubst_le_dx, conj/
qed.

lemma fsubst_and_rc_sn (t) (u) (v):
      ⬕[t∩u←v]t ⇔ ⬕[u←v]t.
/3 width=1 by conj, fsubst_and_rc_sn_sn, fsubst_and_rc_sn_dx/
qed.

lemma grafted_fsubst (t) (u) (v) (p):
      p ⧸ϵ ▵u → p ⧸ϵ ▵v →
      (⋔[p]t) ⇔ ⋔[p]⬕[u←v]t.
/3 width=4 by grafted_fsubst_sn, grafted_fsubst_dx, conj/
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
(*
lemma fsubst_pt_append_refl_sn (t) (p) (u):
      u ⇔ (p●t)[p⋔←u].
#t #p #u @conj #r [| * // * ]
[ /2 width=1 by fsubst_in_comp_true/
| * #s #_ #H1 #H0 destruct
  elim H0 -H0 //
]
qed.

lemma fsubst_empty_rc (t) (u):
      u ⇔ t[𝐞⋔←u].
#t #u @conj #p [| * // * ]
[ /2 width=1 by fsubst_in_comp_true/
| #H1p #H2p elim H2p -H2p //
]
qed.
*)

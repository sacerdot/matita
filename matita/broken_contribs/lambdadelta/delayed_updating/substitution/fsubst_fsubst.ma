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

include "delayed_updating/substitution/fsubst_eq.ma".

(* FOCALIZED SUBSTITUTION ***************************************************)

(* Substitution lemmas with term_le *****************************************)

lemma fsubst_2_nol_le (t) (u1) (u2) (v1) (v2):
      t ≬ u1 → t ≬ u2 → u1 ⧸≬ u2 → u1 ⧸≬ v2 → u2 ⧸≬ v1 →
      ⬕[u1←v1]⬕[u2←v2]t ⊆ ⬕[u2←v2]⬕[u1←v1]t.
#t #u1 #u2 #v1 #v2 #Hu1 #Hu2 #Hnu #Hn12 #Hn21 #p * * [| * * ]
[ #_ #Hp
  @fsubst_in_comp_false
  [ /2 width=1 by fsubst_in_comp_true/
  | /3 width=3 by subset_ol_i/
  ]
| #_ #Hp #Hnp
  @fsubst_in_comp_true [| // ]
  @(subset_ol_eq_repl … u2 … (fsubst_eq …)) [|*: // ]
  /3 width=1 by subset_ol_or_sn_dx, subset_ol_nimp_sn/
| #H1p #Hnp #H2p
  /3 width=1 by fsubst_in_comp_false/
]
qed.

lemma fsubst_2_le_le (t) (u1) (u2) (v1) (v2):
      u2 ⊆ u1 →
      ⬕[u1←⬕[u2←v2]v1]t ⊆ ⬕[u2←v2]⬕[u1←v1]t.
#t #u1 #u2 #v1 #v2 #Hu21 #p * *
[ #Hu1 * *
  [ #Hv1 #p
    /3 width=1 by subset_ol_fsubst_sn, fsubst_in_comp_true/
  | #Hp #Hnp
    /3 width=1 by fsubst_in_comp_false, fsubst_in_comp_true/
  ]
| #Hp #Hnp
  /4 width=1 by fsubst_in_comp_false/
]
qed-.

lemma fsubst_2_le_ge (t) (u1) (u2) (v1) (v2):
      t ≬ u1 → u2 ⊆ u1 →
      ⬕[u2←v2]⬕[u1←v1]t ⊆ ⬕[u1←⬕[u2←v2]v1]t .
#t #u1 #u2 #v1 #v2 #Hu1 #Hv1 #p * * [| * * ]
[ #H0 #Hp
  /4 width=5 by subset_ol_inv_fsubst_sn, fsubst_in_comp_true/
| #_ #Hp #Hnp
  /3 width=1 by fsubst_in_comp_false, fsubst_in_comp_true/
| #Hp #Hnp #_
  /2 width=1 by fsubst_in_comp_false/
]
qed.

(* Substitution lemmas with term_eq *****************************************)

theorem fsubst_2_nol_eq (t) (u1) (u2) (v1) (v2):
        t ≬ u1 → t ≬ u2 → u1 ⧸≬ u2 → u1 ⧸≬ v2 → u2 ⧸≬ v1 →
        ⬕[u1←v1]⬕[u2←v2]t ⇔ ⬕[u2←v2]⬕[u1←v1]t.
#t #u1 #u2 #v1 #v2 #Hu1 #Hu2 #Hnu #Hn12 #Hn21
/5 width=1 by fsubst_2_nol_le, subset_ol_sym, conj/
qed.

theorem fsubst_2_le_eq (t) (u1) (u2) (v1) (v2):
        t ≬ u1 → u2 ⊆ u1 →
        ⬕[u1←⬕[u2←v2]v1]t ⇔ ⬕[u2←v2]⬕[u1←v1]t.
/3 width=1 by fsubst_2_le_ge, fsubst_2_le_le, conj/
qed.

theorem fsubst_3_le_eq (t) (u1) (u2) (u3) (v1) (v2) (v3):
        t ≬ u1 → t ≬ u2 → u1 ⧸≬ u2 → u1 ⧸≬ v2 → u2 ⧸≬ v1 → u3 ⊆ u1 →
        ⬕[u1←⬕[u3←v3]v1]⬕[u2←v2]t ⇔ ⬕[u3←v3]⬕[u2←v2]⬕[u1←v1]t.
#t #u1 #u2 #u3 #v1 #v2 #v3 #Hu1 #Hu2 #Hnu #Hn12 #Hn21 #Hu31
@(subset_eq_trans ????? (fsubst_eq_repl …))
[ @fsubst_2_le_eq //
  @(subset_ol_eq_repl … (fsubst_eq … Hu2) … (subset_eq_refl …))
  /5 width=1 by subset_ol_nimp_sn, subset_ol_or_sn_dx, subset_ol_sym/
|2,3: @subset_eq_refl
|4: @(fsubst_2_nol_eq … Hu1 Hu2 Hnu Hn12 Hn21)
|5,6,7: skip
]
qed.

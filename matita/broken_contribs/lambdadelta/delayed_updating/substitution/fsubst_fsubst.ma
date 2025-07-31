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

include "ground/subsets/subset_nimply_eq.ma".
include "ground/subsets/subset_nimply_ol.ma".
include "ground/subsets/subset_nimply_or_eq.ma".
include "delayed_updating/substitution/fsubst_eq.ma".

(* FOCALIZED SUBSTITUTION ***************************************************)

(* Substitution lemmas with term_le *****************************************)

lemma fsubst_2_swap_le (t) (u1) (u2) (v1) (v2):
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

lemma fsubst_2_distr_le (t) (u1) (u2) (v1) (v2):
      (t ⧵ u1) ⧸≬ u2 →
      ⬕[u1←⬕[u2←v2]v1]t ⊆ ⬕[u2←v2]⬕[u1←v1]t.
#t #u1 #u2 #v1 #v2 #Hnu12 #p * *
[ #Hu1 * *
  [ #Hv1 #p -Hnu12
    /3 width=1 by subset_ol_fsubst_sn, fsubst_in_comp_true/
  | #Hp #Hnp -Hnu12
    /3 width=1 by fsubst_in_comp_false, fsubst_in_comp_true/
  ]
| #Hp #Hnp
  @fsubst_in_comp_false
  [ /2 width=1 by fsubst_in_comp_false/
  | #H0p @Hnu12 -Hnu12
    /4 width=3 by subset_ol_i, subset_and_in/
  ]
]
qed-.

lemma fsubst_2_distr_ge (t) (u1) (u2) (v1) (v2):
      t ≬ u1 → (t ⧵ u1) ⧸≬ u2 →
      ⬕[u2←v2]⬕[u1←v1]t ⊆ ⬕[u1←⬕[u2←v2]v1]t.
#t #u1 #u2 #v1 #v2 #Hu1 #Hnu12 #p * * [| * * ]
[ #H0 #Hp
  /4 width=5 by subset_ol_inv_fsubst_sn, fsubst_in_comp_true/
| #_ #Hp #Hnp
  /3 width=1 by fsubst_in_comp_false, fsubst_in_comp_true/
| #Hp #Hnp #_
  /2 width=1 by fsubst_in_comp_false/
]
qed.

(* Substitution lemmas with term_eq *****************************************)

theorem fsubst_2_swap_eq (t) (u1) (u2) (v1) (v2):
        t ≬ u1 → t ≬ u2 → u1 ⧸≬ u2 → u1 ⧸≬ v2 → u2 ⧸≬ v1 →
        ⬕[u1←v1]⬕[u2←v2]t ⇔ ⬕[u2←v2]⬕[u1←v1]t.
#t #u1 #u2 #v1 #v2 #Hu1 #Hu2 #Hnu #Hn12 #Hn21
/5 width=1 by fsubst_2_swap_le, subset_ol_sym, conj/
qed.

theorem fsubst_2_distr_eq (t) (u1) (u2) (v1) (v2):
        t ≬ u1 → (t ⧵ u1) ⧸≬ u2 →
        ⬕[u1←⬕[u2←v2]v1]t ⇔ ⬕[u2←v2]⬕[u1←v1]t.
/3 width=1 by fsubst_2_distr_ge, fsubst_2_distr_le, conj/
qed.

theorem fsubst_3_distr_eq (t) (u1) (u2) (u3) (v1) (v2) (v3):
        t ≬ u1 → t ≬ u2 → u1 ⧸≬ u2 → u1 ⧸≬ v2 → u2 ⧸≬ v1 →
        (v2 ⧵ u1) ⧸≬ u3 → ((t ⧵ u2) ⧵ u1) ⧸≬ u3 →
        ⬕[u1←⬕[u3←v3]v1]⬕[u2←v2]t ⇔ ⬕[u3←v3]⬕[u2←v2]⬕[u1←v1]t.
#t #u1 #u2 #u3 #v1 #v2 #v3 #Hu1 #Hu2 #Hnu #Hn12 #Hn21 #H1u3 #H2u3
@(subset_eq_trans ????? (fsubst_eq_repl …))
[ @fsubst_2_distr_eq [| #H0 ]
  [ @(subset_ol_eq_repl … (fsubst_eq … Hu2) … (subset_eq_refl …))
    /5 width=1 by subset_ol_nimp_sn, subset_ol_or_sn_dx, subset_ol_sym/
  | @(subset_nol_or_sn … H1u3 H2u3) -H1u3 -H2u3
    @(subset_ol_eq_repl … H0) -H0 [| // ]
    @(subset_eq_canc_dx … (subset_nimp_or_sn …))
    @subset_nimp_eq_repl
    /3 width=1 by fsubst_eq, subset_eq_sym/
  ]
|2,3: @subset_eq_refl
|4: @(fsubst_2_swap_eq … Hu1 Hu2 Hnu Hn12 Hn21)
|5,6,7: skip
]
qed.

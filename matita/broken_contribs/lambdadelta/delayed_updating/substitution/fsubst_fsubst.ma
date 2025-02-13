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

include "ground/subsets/subset_nimply_ol.ma".
include "delayed_updating/substitution/fsubst_eq.ma".

(* FOCALIZED SUBSTITUTION ***************************************************)

(* Substitutio lemmas *******************************************************)

lemma fsubst_fsubst_nol_le (t) (u1) (u2) (v1) (v2):
      t ≬ u1 → t ≬ u2 → u1 ⧸≬ u2 → u1 ⧸≬ v2 → u2 ⧸≬ v1 →
      ⬕[u1←v1]⬕[u2←v2]t ⊆ ⬕[u2←v2]⬕[u1←v1]t.
#t #u1 #u2 #v1 #v2 #Hu1 #Hu2 #Hnu #Hn12 #Hn21 #p * * [| * * ]
[ #_ #Hp
  @fsubst_in_comp_false [| /3 width=3 by subset_ol_i/ ]
  @fsubst_in_comp_true //
| #_ #Hp #Hnp
  @fsubst_in_comp_true [| // ]
  @(subset_ol_eq_repl … u2 … (fsubst_eq …)) [|*: // ]
  /3 width=1 by subset_ol_or_sn_dx, subset_ol_nimp_sn/
| #H1p #Hnp #H2p
  /3 width=1 by fsubst_in_comp_false/
]
qed.

lemma fsubst_fsubst_nol_eq (t) (u1) (u2) (v1) (v2):
      t ≬ u1 → t ≬ u2 → u1 ⧸≬ u2 → u1 ⧸≬ v2 → u2 ⧸≬ v1 →
      ⬕[u1←v1]⬕[u2←v2]t ⇔ ⬕[u2←v2]⬕[u1←v1]t.
#t #u1 #u2 #v1 #v2 #Hu1 #Hu2 #Hnu #Hn12 #Hn21
/5 width=1 by fsubst_fsubst_nol_le, subset_ol_sym, conj/
qed.

lemma fsubst_fsubst_nol_inv_eq (t) (t1) (t2) (t3) (t4) (u1) (u2) (v1) (v2) (y1) (y2):
      t ≬ u1 → t ≬ u2 → u1 ⧸≬ u2 → u1 ⧸≬ v2 → u2 ⧸≬ v1 →
      v1 ⇔ y1 → v2 ⇔ y2 →
      ⬕[u2←v2]t ⇔ t1 → ⬕[u1←v1]t ⇔ t2 →
      ⬕[u1←y1]t1 ⇔ t3 → ⬕[u2←y2]t2 ⇔ t4 →
      t3 ⇔ t4.
#t #t1 #t2 #t3 #t4 #u1 #u2 #v1 #v2 #y1 #y2
#Hu1 #Hu2 #Hnu #Hn12 #Hn21 #Hvy1 #Hvy2 #Ht1 #Ht2 #Ht3 #Ht4
lapply (fsubst_fsubst_nol_eq … Hu1 Hu2 Hnu Hn12 Hn21) -Hu1 -Hu2 -Hnu -Hn12 -Hn21 #Ht
@(subset_eq_repl … Ht3 … Ht4) -t3 -t4
@(subset_eq_repl … Ht) -Ht
/2 width=1 by fsubst_eq_repl/
qed-.

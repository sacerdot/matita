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

(* Substitution lemmas with term_le *****************************************)

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

lemma fsubst_fsubst_le_le (t) (u1) (u2) (v1) (v2):
      t ≬ u1 → t ≬ u2 → u1 ⧸≬ u2 → v1 ⊆ v2 →
      ⬕[u1←v1]⬕[u2←⬕[u1←v1]v2]t ⊆ ⬕[u2←v2]⬕[u1←v1]t.
#t #u1 #u2 #v1 #v2 #Hu1 #Hu2 #Hnu #Hv12 #p * * [| * * ]
[ #_ #Hp
  @fsubst_in_comp_true [| /2 width=1 by/ ]
  @(subset_ol_eq_repl … u2 … (fsubst_eq …)) [|*: // ]
  /3 width=1 by subset_ol_or_sn_dx, subset_ol_nimp_sn/
| #_ #Hp #Hnp
  lapply (fsubst_le_or_sn_dx … Hp) -Hp #Hp
  @fsubst_in_comp_true [| /2 width=5 by subset_le_or_sn/ ]
  @(subset_ol_eq_repl … u2 … (fsubst_eq …)) [|*: // ]
  /3 width=1 by subset_ol_or_sn_dx, subset_ol_nimp_sn/
| #H1p #H2p #Hnp
  /3 width=1 by fsubst_in_comp_false/
]
qed.
(*
lemma fsubst_fsubst_le_ge (t) (u1) (u2) (v1) (v2):
      t ≬ u1 → t ≬ u2 → u1 ⧸≬ u2 → v1 ⊆ v2 →
      (∀p. Decidable (p ϵ v1)) →
      ⬕[u2←v2]⬕[u1←v1]t ⊆ ⬕[u1←v1]⬕[u2←⬕[u1←v1]v2]t.
#t #u1 #u2 #v1 #v2 #Hu1 #Hu2 #Hnu #_ (* Hv12 *) #Hv2
#p * * [| * * ]
[ #_ #Hp elim (Hv2 p) -Hv2 #Hnp
  [ @fsubst_in_comp_true [| // ]
    @(subset_ol_eq_repl … u1 … (fsubst_eq …)) [|*: // ]
    /5 width=1 by subset_ol_or_sn_dx, subset_ol_nimp_sn, subset_ol_sym/
  | @fsubst_in_comp_false [| // ]

    @subset_ol_or_sn_dx
    @subset_ol_nimp_sn // /3 width=3 by subset_ol_sym/

*)
(* Substitution lemmas with term_eq *****************************************)

lemma fsubst_fsubst_nol_eq (t) (u1) (u2) (v1) (v2):
      t ≬ u1 → t ≬ u2 → u1 ⧸≬ u2 → u1 ⧸≬ v2 → u2 ⧸≬ v1 →
      ⬕[u1←v1]⬕[u2←v2]t ⇔ ⬕[u2←v2]⬕[u1←v1]t.
#t #u1 #u2 #v1 #v2 #Hu1 #Hu2 #Hnu #Hn12 #Hn21
/5 width=1 by fsubst_fsubst_nol_le, subset_ol_sym, conj/
qed.

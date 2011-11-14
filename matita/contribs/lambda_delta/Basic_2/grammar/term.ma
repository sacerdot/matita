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

include "Basic_2/grammar/item.ma".

(* TERMS ********************************************************************)

(* terms *)
inductive term: Type[0] ≝
  | TAtom: item0 → term               (* atomic item construction *)
  | TPair: item2 → term → term → term (* binary item construction *)
.

interpretation "sort (term)" 'Star k = (TAtom (Sort k)).

interpretation "local reference (term)" 'LRef i = (TAtom (LRef i)).

interpretation "global reference (term)" 'GRef p = (TAtom (GRef p)).

interpretation "term construction (atomic)" 'SItem I = (TAtom I).

interpretation "term construction (binary)" 'SItem I T1 T2 = (TPair I T1 T2).

interpretation "term binding construction (binary)" 'SBind I T1 T2 = (TPair (Bind I) T1 T2).

interpretation "term flat construction (binary)" 'SFlat I T1 T2 = (TPair (Flat I) T1 T2).

(* Basic inversion lemmas ***************************************************)

lemma discr_tpair_xy_x: ∀I,T,V. 𝕔{I} V. T = V → False.
#I #T #V elim V -V
[ #J #H destruct
| #J #W #U #IHW #_ #H destruct
(*
 (generalize in match e1) -e1 >e0 normalize
*) -I /2/ (**) (* destruct: one quality is not simplified, the destucted equality is not erased *)
]
qed-.

(* Basic_1: was: thead_x_y_y *)
lemma discr_tpair_xy_y: ∀I,V,T. 𝕔{I} V. T = T → False.
#I #V #T elim T -T
[ #J #H destruct
| #J #W #U #_ #IHU #H destruct -I V /2/ (**) (* destruct: the destucted equality is not erased *)
]
qed-.

(* Basic properties *********************************************************)

(* Basic_1: was: term_dec *)
axiom term_eq_dec: ∀T1,T2:term. Decidable (T1 = T2).

(* Basic_1: removed theorems 3:
            not_void_abst not_abbr_void not_abst_void
*)

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

include "ground/xoa/ex_1_2.ma".
include "ground/lib/list_append.ma".
include "ground/subsets/subset.ma".
include "ground/notation/functions/subset_x_2.ma".
include "ground/notation/functions/circled_collection_f_1.ma".

(* SUBSET WITH LISTED ELEMENTS **********************************************)

definition subset_listed (A) (l): 𝒫❨A❩ ≝
           {a | ∃∃l1,l2. l1 ⨁ a ⨮ l2 = l}.

interpretation
  "listed (subset)"
  'SubsetX A l = (subset_listed A l).

interpretation
  "empty (subset)"
  'CircledCollectionF A = (subset_listed A (list_empty A)).

(* Basic constructions ******************************************************)

lemma subset_in_listed (A) (l1) (l2) (a):
      a ϵ{A} 𝐗❨l1 ⨁ a ⨮ l2❩.
/2 width=3 by ex1_2_intro/
qed.

lemma subset_in_listed_lcons_sx (A) (l) (a):
      a ϵ{A} 𝐗❨a ⨮ l❩.
#A #l #a
>(list_append_empty_sx … (a⨮l)) //
qed.

lemma subset_in_listed_lcons_dx (A) (l) (a) (b):
      a ϵ 𝐗❨l❩ → a ϵ{A} 𝐗❨b⨮l❩.
#A #l #a #b * #l1 #l2 #H0 destruct //
qed.

(* Basic inversions *********************************************************)

lemma subset_nin_inv_empty (A) (a):
      a ⧸ϵ{A} Ⓕ.
#A #a * #l1 #l2 #H0
elim (eq_inv_list_append_empty … H0) -H0 #_ #H0 destruct
qed-.

lemma subset_in_inv_listed_lcons (A) (l) (a) (b):
      a ϵ{A} 𝐗❨b⨮l❩ →
      ∨∨ a = b | a ϵ 𝐗❨l❩.
#A #l #a #b * #l1 #l2 #H0
elim (eq_inv_list_lcons_append ????? (sym_eq … H0)) -H0 *
[ #H1 #H2 destruct
  /2 width=1 by or_introl/
| #l0 #H1 #H2 destruct
  /2 width=1 by or_intror/
]
qed-.

(* Advanced properties ******************************************************)

lemma subset_in_listed_dec (A:Type[0]):
      (∀a1,a2. Decidable … (a1 ={A} a2)) →
      ∀a,l. Decidable … (a ϵ{A} 𝐗❨l❩).
#A #HA #a #l elim l -l
[ @or_intror
  @subset_nin_inv_empty
| #b #l * #Ha
  [ /3 width=1 by subset_in_listed_lcons_dx, or_introl/
  | elim (HA a b) -HA #Hab destruct
    [ /2 width=1 by or_introl/
    | @or_intror #H0
      elim (subset_in_inv_listed_lcons ???? H0) -H0
      /2 width=1 by/
    ]
  ]
]
qed-.

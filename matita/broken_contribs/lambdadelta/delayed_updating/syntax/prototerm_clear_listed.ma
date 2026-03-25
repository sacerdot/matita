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

include "ground/subsets/subset_eq.ma".
include "ground/subsets/subset_listed_le.ma".
include "delayed_updating/syntax/paths_clear.ma".
include "delayed_updating/syntax/prototerm_clear.ma".

(* CLEARED PROTOTERM ********************************************************)

(* Constructions with subset_listed and subset_le ***************************)

lemma term_clear_empty_le (t):
      (⓪Ⓕ) ⊆ t.
#t #x0 * #x #Hx #_
elim (subset_nin_inv_empty ?? Hx)
qed.

lemma term_clear_listed_ge (ps):
      (𝐗❨⓪ps❩) ⊆ ⓪𝐗❨ps❩.
#ps elim ps -ps
[ <paths_clear_empty //
| #p #ps #IH <paths_clear_lcons #x0 #Hx0
  elim (subset_in_inv_listed_lcons ???? Hx0) -Hx0 #Hx0 destruct
  [ /3 width=1 by in_comp_term_clear/
  | lapply (IH … Hx0) -IH -Hx0 * #x #Hx #H0 destruct
    /3 width=1 by in_comp_term_clear, subset_in_listed_lcons_dx/
  ]
]
qed.

lemma term_clear_listed_le (ps):
      (⓪𝐗❨ps❩) ⊆ 𝐗❨⓪ps❩.
#ps elim ps -ps //
#p #ps #IH #x0 * #x #Hx #H0 <paths_clear_lcons
elim (subset_in_inv_listed_lcons ???? Hx) -Hx #Hx destruct
/4 width=1 by in_comp_term_clear, subset_in_listed_lcons_dx/
qed.

(* Constructions with subset_listed and subset_eq ***************************)

lemma term_clear_listed_eq (ps):
      (𝐗❨⓪ps❩) ⇔ ⓪𝐗❨ps❩.
/3 width=1 by conj, term_clear_listed_ge, term_clear_listed_le/
qed.

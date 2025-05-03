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

include "ground/subsets/subset.ma".
include "ground/relocation/fb/fbr_eq.ma".
include "ground_2B/notation/functions/subset_i_0.ma".

(* IDENTITY CLASS FOR FINITE RELOCATION MAPS WITH BOOLEANS ******************)

definition fbr_isid: 𝒫❨𝔽𝔹❩ ≝
           {f | f ≐ ⫯f}.

interpretation
  "identity class (finite relocation maps with booleans)"
  'SubsetI = (fbr_isid).

(* Basic inversions *********************************************************)

lemma fbr_isid_inv_push (f):
      (⫯f) ϵ 𝐈 → f ϵ 𝐈.
/2 width=1 by fbr_eq_inv_push_bi/
qed-.

lemma fbr_isid_inv_next (f):
      ↑f ϵ 𝐈 → ⊥.
/2 width=3 by fbr_eq_inv_next_push/
qed-.

(* Basic eliminations *******************************************************)

lemma fbr_isid_ind (Q: predicate …): 
      (Q (𝐢)) → (∀f. f ϵ 𝐈 → Q f → Q (⫯f)) →
      ∀f. f ϵ 𝐈 → Q f.
#Q #IH1 #IH2 #f
elim f -f // * #f #IH #H0
[ elim (fbr_isid_inv_next … H0)
| lapply (fbr_isid_inv_push … H0) -H0 #H0
  /3 width=1 by/
]
qed-.

(* Advanced inversions ******************************************************)

lemma fbr_isid_inv_eq_id_sn (f):
      f ϵ 𝐈 → (𝐢) ≐ f.
#f #H0
@(fbr_isid_ind … H0) -f // #f #_ #IH
/2 width=1 by fbr_eq_id_push/
qed-.

(* Main inversions **********************************************************)

theorem fbr_isid_inv_eq_repl (f1) (f2):
        f1 ϵ 𝐈 → f2 ϵ 𝐈 → f1 ≐ f2.
/3 width=3 by fbr_isid_inv_eq_id_sn, fbr_eq_canc_sn/
qed-.

(* Basic constructions ******************************************************)

lemma fbr_isid_id:
      (𝐢) ϵ 𝐈.
//
qed.

lemma fbr_isid_push (f):
      f ϵ 𝐈 → ⫯f ϵ 𝐈.
/2 width=1 by fbr_eq_rcons_bi/
qed.

(* Advanced constructions ***************************************************)

lemma fbr_eq_id_sn_isid (f):
      (𝐢) ≐ f → f ϵ 𝐈.
#f #H0
@(fbr_eq_repl ???? H0)
/2 width=3 by fbr_eq_id_push/
qed.

lemma fbr_isid_eq_repl_back:
      replace_1_back … fbr_eq fbr_isid.
#f1 #H #f2 #H0
/4 width=3 by fbr_eq_id_sn_isid, fbr_isid_inv_eq_id_sn, fbr_eq_canc_dx/
qed-.

lemma fbr_isid_eq_repl_fwd:
      replace_1_fwd … fbr_eq fbr_isid.
/3 width=3 by fbr_isid_eq_repl_back, fbr_eq_sym/
qed-.

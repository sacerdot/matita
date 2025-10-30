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

include "ground/xoa/ex_3_1.ma".
include "ground/arith/wf1_ind_nlt.ma".
include "ground/lib/list_length.ma".
include "ground/subsets/subset_or_lt.ma".
include "ground/subsets/subset_nimply_ol_le.ma".
include "ground/subsets/subset_nimply_or_le.ma".
include "ground/subsets/subset_listed_ol_1.ma".
include "ground/subsets/subset_listed_inhabited.ma".

(* SUBSET WITH LISTED ELEMENTS **********************************************)

(* Constructions with subset_lt *********************************************)

lemma subset_lt_listed_lcons_dx (A) (l) (a):
      a ⧸ϵ 𝐗❨l❩ → 𝐗❨l❩ ⊂ 𝐗{A}❨a⨮l❩.
/4 width=3 by subset_listed_le_lcons_dx, subset_lt_mk, subsets_inh_in, subset_in_nimp/
qed.

lemma subset_lt_listed_lcons_bi (A) (a) (l1) (l2):
      a ⧸ϵ{A} 𝐗❨l2❩ → 𝐗❨l1❩ ⊂ 𝐗❨l2❩ → 𝐗❨a⨮l1❩ ⊂ 𝐗❨a⨮l2❩.
#A #a #l1 #l2 #Ha #Hl
@(subset_le_lt_trans … (subset_le_listed_lcons_or …))
@(subset_lt_le_trans … (subset_le_or_listed_lcons …))
/3 width=5 by subset_nol_inv_single_sx, subset_lt_or_bi_sx/
qed.

(* Inversions with subset_lt ************************************************)

lemma subset_lt_inv_empty_dx (A) (u):
      u ⧸⊂ Ⓕ{A}.
#A #u * #_ #H0
lapply (subsets_inh_le_repl_fwd … H0 ?) -H0 [ // | skip ]
/2 width=2 by subset_nin_inv_empty_inh/
qed-.

(* Destructions with subset_lt **********************************************)

lemma subset_lt_des_listed_dx (A:Type[0]) (u) (l2):
      (∀a1,a2. Decidable … (a1 ={A} a2)) →
      u ⊂ 𝐗{A}❨l2❩ →
      ∃∃l1. u ⊆ 𝐗❨l1❩ & 𝐗❨l1❩ ⊂ 𝐗{A}❨l2❩ & ❘l1❘ < ❘l2❘.
#A #u #l2 #HA * #H1u #H0
elim (subsets_inh_inv_in … H0) -H0 #b * #H1b #H2b
generalize in match H2b; -H2b
generalize in match H1b; -H1b
generalize in match H1u; -H1u
generalize in match u; -u
elim l2 -l2 [ #u #_ #H1b #_ | #a #l2 #IH #u #H1u #H1b #H2b ]
[ elim (subset_nin_inv_empty ?? H1b)
| elim (HA a b) #Hab destruct
  [ lapply (subset_le_inv_listed_lcons_dx_nin … H2b H1u) -H1u #H1u
    elim (subset_in_listed_dec … HA b l2) -HA -H1b #Hb
    [ elim (IH … H1u Hb H2b) -IH -H1u -Hb -H2b #l1 #Hu #H1l #H2l
      @(ex3_intro … Hu) -Hu (**) (* auto fails *)
      [ @(subset_lt_le_trans … H1l) -H1l //
      | /2 width=3 by nlt_trans/
      ]
    | /4 width=5 by subset_lt_listed_lcons_dx, ex3_intro/
    ]
  | elim (subset_in_listed_dec … a l2) [3: // ] #Ha
    [ lapply (subset_le_trans … H1u … (subset_le_listed_lcons_sx …)) -H1u [ // ] #H1u
      lapply (subset_in_le_trans ???? H1b (subset_le_listed_lcons_sx …)) -H1b [ // ] #H1b
      elim (IH … H1u H1b H2b) -b -H1u #l1 #Hl1 #H1l #H2l
      /4 width=4 by subset_listed_le_lcons_dx, subset_lt_le_trans, nlt_succ_dx_trans, ex3_intro/
    | lapply (subset_single_le_sx ??? H1b) -H1b #H1b
      lapply (subset_le_trans … H1u … (subset_le_listed_lcons_or …)) -H1u #H1u
      lapply (subset_le_trans … H1b … (subset_le_listed_lcons_or …)) -H1b #H1b
      lapply (subset_le_nimp_bi ?? (❴a❵) ? (❴a❵) H1u ?) -H1u // #H1u
      lapply (subset_le_nimp_bi ?? (❴a❵) ? (❴a❵) H1b ?) -H1b // #H1b
      lapply (subset_le_trans … H1u … (subset_le_nimp_or_sx_refl_sx …)) -H1u #H1u
      lapply (subset_le_trans … H1b … (subset_le_nimp_or_sx_refl_sx …)) -H1b #H1b
      lapply (subset_le_trans ??? (subset_le_nimp_dx_refl_sx_bck ????) ? H1b) -H1b
      [ /3 width=5 by subset_nol_inv_single_bi/ ] #H1b
      lapply (subset_le_inv_single_sx ??? H1b) -H1b #H1b
      elim (IH … H1u H1b …) -IH -H1u -H1b
      [ -b | @(subset_nin_ge_trans ???? H2b) -H2b // ] #l1 #Hl1 #H1l #H2l
      lapply (subset_or_le_repl A (❴a❵) (❴a❵) … Hl1) [ // ] -Hl1 #Hl1
      lapply (subset_le_trans ??? (subset_le_or_dx_nimp_dx_refl_bi ????) ? Hl1) -Hl1
      [ /2 width=1 by subset_in_listed_dec/ ] #Hl1
      lapply (subset_le_trans … Hl1 … (subset_le_or_listed_lcons …)) -Hl1 #Hl1
      /4 width=5 by subset_lt_listed_lcons_bi, nlt_succ_bi, ex3_intro/
    ]
  ]
]
qed-.

(* Eliminations with subset_lt **********************************************)

lemma subset_listed_ind_lt_le (A:Type[0]) (Q:predicate …): (**)
      (∀a1,a2. Decidable … (a1 ={A} a2)) →
      (∀l2. (∀l1. 𝐗❨l1❩ ⊂ 𝐗❨l2❩ → Q l1) → Q l2) →
      ∀l2,l1. 𝐗{A}❨l1❩ ⊆ 𝐗❨l2❩ → Q l1.
#A #Q #HA #IH0 #l2 @(wf1_ind_nlt … (list_length A) … l2) -l2
#n #IH #l2 #H0 * [| #a #l1 ] #Hl12 destruct
[ @IH0 -IH0 -IH -l2 #l1 #H0
  elim (subset_lt_inv_empty_dx … H0)
| @IH0 -IH0 #l #Hl1
  lapply (subset_lt_le_trans … Hl1 Hl12) -l1 -a #Hl2
  elim (subset_lt_des_listed_dx … HA Hl2) -Hl2 #l1 #Hl1 #_ #Hl12
  /2 width=3 by/
]
qed-.

lemma subset_listed_ind_lt (A:Type[0]) (Q:predicate …): (**)
      (∀a1,a2. Decidable … (a1 ={A} a2)) →
      (∀l2. (∀l1. 𝐗{A}❨l1❩ ⊂ 𝐗❨l2❩ → Q l1) → Q l2) →
      ∀l2. Q l2.
#A #Q #HA #IH #l2
@(subset_listed_ind_lt_le … HA IH l2) -Q -HA //
qed-.

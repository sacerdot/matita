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

include "delayed_updating/syntax/preterm.ma".
include "delayed_updating/syntax/prototerm_length.ma".
include "delayed_updating/syntax/path_structure.ma".
include "ground/lib/list_weight_2_rcons.ma".
include "ground/arith/wf2_ind_nlt.ma".

(* PRETERM ******************************************************************)

(* Destructions with path_structure *****************************************)

lemma term_slice_des_structure_bi (t) (p) (q1) (q2):
      t ϵ 𝐓 → p●q1 ϵ ▵t → p●q2 ϵ ▵t → ⊗q1 ϵ ↑⊗q2 →
      ∨∨ q1 ϵ ↑q2 | q2 ϵ ↑q1.
#t #p #q1 #q2 #Ht
generalize in match p; -p
@(wf2_ind_nlt … (list_weight_2 …) … q1 q2) -q1 -q2
#n #IH #q1 @(list_ind_rcons … q1) -q1
[ /3 width=3 by ex2_intro, or_intror/ ]
#q1 #l1 #_ #q2 @(list_ind_rcons … q2) -q2
[ /3 width=3 by ex2_intro, or_introl/ ]
#q2 #l2 #_ <list_weight_2_rcons_sn <list_weight_2_rcons_dx
#H0 #p #Hq1 #Hq2 #Hq destruct
elim (label_is_d l1)
[ * #k1 #H0 destruct
  lapply (term_root_d_post t … p l2 k1 ??)
  [4:|*: /2 width=2 by term_in_root_append_des_sn/ ]
  #H0 destruct
  <structure_d_sn in Hq; <structure_d_sn #Hq
  elim (IH ??? (p◖𝗱k1) … Hq) -IH -Hq //
  /3 width=1 by term_slice_append_sn, or_introl, or_intror/
]
elim (label_is_d l2)
[ * #k2 #H0 destruct
  lapply (term_root_d_post t … p l1 k2 ??)
  [4:|*: /2 width=2 by term_in_root_append_des_sn/ ]
  #H0 destruct
  <structure_d_sn in Hq; <structure_d_sn #Hq
  elim (IH ??? (p◖𝗱k2) … Hq) -IH -Hq //
  /3 width=1 by term_slice_append_sn, or_introl, or_intror/
]
#Hl2 #Hl1
<(structure_lcons_inner … Hl1) in Hq; <(structure_lcons_inner … Hl2) #Hq
elim (term_slice_inv_lcons_bi … Hq) -Hq -Hl1 -Hl2 #H0 #Hq destruct
elim (IH ??? (p◖l2) … Hq) -IH -Hq //
/3 width=1 by term_slice_append_sn, or_introl, or_intror/
qed-.

lemma term_root_eq_des_structure_bi (t) (p) (q1) (q2):
      t ϵ 𝐓 → p●q1 ϵ ▵t → p●q2 ϵ ▵t → ⊗q1 = ⊗q2 →
      ∨∨ ∃∃r2. q1 = q2●r2 & 𝐞 = ⊗r2
      |  ∃∃r1. q2 = q1●r1 & 𝐞 = ⊗r1.
#t #p #q1 #q2 #Ht #Hq1 #Hq2 #Hq
elim (term_slice_des_structure_bi … q1 q2 Ht …) // -t
* #r #_ #H0 destruct
<structure_append in Hq; #Hq
[ lapply (eq_inv_list_append_dx_dx_refl … (sym_eq … Hq)) -Hq #Hq
  /3 width=3 by ex2_intro, or_introl/
| lapply (eq_inv_list_append_dx_dx_refl … Hq) -Hq #Hq
  /3 width=3 by ex2_intro, or_intror/
]
qed-.

(* Inversions with path_structure *******************************************)

lemma term_root_eq_inv_structure_L_bi (t) (p) (q1) (q2):
      t ϵ 𝐓 → p●q1◖𝗟 ϵ ▵t → p●q2◖𝗟 ϵ ▵t →
      ⊗q1 = ⊗q2 → q1 = q2.
#t #p #q1 #q2 #Ht #Hq1 #Hq2 #Hq
elim (term_root_eq_des_structure_bi … p q1 q2 Ht)
[3: // | 4,5: @(term_in_root_append_des_sn … (𝐞◖𝗟)) // ] -Hq *
#r @(list_ind_rcons … r) -r [2,4: #r #l #_ ] #Hq #Hr //
elim (eq_inv_empty_structure_lcons … Hr) -Hr * #k #H0 #_ destruct
[ lapply (term_root_d_post … Ht (p●q2) (𝗟) k ??)
| lapply (term_root_d_post … Ht (p●q1) (𝗟) k ??)
]
[1,4: @(term_in_root_append_des_sn … (r◖𝗟)) //
|2,5: //
|3,6: -Hq1 -Hq2 #H0 destruct
]
qed-.

lemma term_root_eq_inv_structure_bi (t) (q1) (q2):
      t ϵ 𝐓 → q1 ϵ ▵t → q2 ϵ ▵t → ❘q1❘ = ❘q2❘ →
      ⊗q1 = ⊗q2 → q1 = q2.
#t #q1 #q2 #Ht #Hq1 #Hq2 #H1q #H2q
elim (term_slice_des_structure_bi … q1 q2 Ht … ) // -t -H2q #H2q
<(term_slice_eq_inv_length_bi … H2q) -H2q //
qed-.

(* Note: different complete paths have different structure *)
lemma term_structure_inj (t) (q1) (q2):
      t ϵ 𝐓 → q1 ϵ t → q2 ϵ t → ⊗q1 = ⊗q2 → q1 = q2.
#t #q1 #q2 #Ht #Hq1 #Hq2 #Hq
elim (term_slice_des_structure_bi … q1 q2 Ht …) // -Hq
[3,4,5: /2 width=3 by term_in_comp_root/ ] #H0
lapply (term_complete_post … Ht … H0) -Ht -H0 //
qed-.

(* Note: a generalization of term_root_d_post *)
lemma term_comp_inv (t) (q1) (q2) (p):
      t ϵ 𝐓 → p●q1 ϵ t → p●q2 ϵ t →
      (𝐞) = ⊗q2 → q1 = q2.
#t
#q1 @(list_ind_rcons … q1) -q1 [| #q1 #l1 #IH ]
#q2 @(list_ind_rcons … q2) -q2 [2,4: #q2 #l2 #_]
#p #Ht #Hq1 #Hq2 #Hq
[ lapply (term_complete_post … Ht … Hq2 Hq1 ?) -t -Hq // #H0
  lapply (eq_inv_list_append_dx_dx_refl … (sym_eq … H0)) -H0 #H0
  elim (eq_inv_list_empty_rcons ??? H0)
| <structure_append in Hq; #H0
  elim (eq_inv_list_empty_append … H0) -H0 #Hq #H0
  elim (eq_inv_empty_structure_singleton … H0) -H0 #k2 #H0 destruct
  lapply (term_root_d_post … Ht p l1 k2 ? ?)
  [1,2: /2 width=2 by term_in_root/ ] #H0 destruct
  <list_append_rcons_sn in Hq1; #Hq1
  <list_append_rcons_sn in Hq2; #Hq2
  <(IH … Hq1 Hq2) -IH -Hq1 -Hq2 //
| //
| lapply (term_complete_post … Ht … Hq1 Hq2 ?) -t -Hq // #H0
  lapply (eq_inv_list_append_dx_dx_refl … (sym_eq … H0)) -H0 #H0
  elim (eq_inv_list_empty_rcons ??? H0)
]
qed-.

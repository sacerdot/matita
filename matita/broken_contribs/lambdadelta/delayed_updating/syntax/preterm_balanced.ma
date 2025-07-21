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

include "delayed_updating/syntax/path_balanced_ind.ma".
include "delayed_updating/syntax/preterm.ma".

(* PRETERM ******************************************************************)

(* Auxiliary inversions *****************************************************)

(* Note this depends on term_root_L_post *)
lemma term_in_comp_pbc_L_inj_aux (t) (p) (b1) (b2) (q1) (q2):
      t ϵ 𝐓 →
      p●𝐞●𝗟◗q1 ϵ t → p●(𝗔◗(b1◖𝗟)●b2)●𝗟◗q2 ϵ t → ⊥.
#t #p #b1 #b2 #q1 #q2 #Ht
<list_append_empty_dx <path_append_pAbLq_12 #H1t #H2t
lapply (term_root_L_post … Ht p (𝗔) ??)
[1,2: /2 width=2 by term_in_root/ ] -t -p -b1 -b2-q1 -q2
#H0 destruct
qed-.

(* Main destructions with pbc ***********************************************)

theorem term_in_comp_pbc_L_inj:
        ∀t. t ϵ 𝐓 → ∀b1. b1 ϵ 𝐁 → ∀b2. b2 ϵ 𝐁 →
        ∀p,q1,q2. p●b1●𝗟◗q1 ϵ t → p●b2●𝗟◗q2 ϵ t →
        b1 = b2.
#t #Ht #b1 #Hb1 @(pbc_ind_sn … Hb1) -b1
[ #b2 #Hb2 #p #q1 #q2 #H1 #H2
  elim (pbc_inv_gen_sn … Hb2) -Hb2 [ // ] *
  #c3 #c4 #_ #_ #H0 destruct
  elim (term_in_comp_pbc_L_inj_aux … Ht H1 H2)
| #c1 #c2 #_ #_ #IH1 #IH2 #b2 #Hb2 #p #q1 #q2 #H1 #H2
  elim (pbc_inv_gen_sn … Hb2) -Hb2
  [ #H0 destruct -IH1 -IH2
    elim (term_in_comp_pbc_L_inj_aux … Ht H2 H1)
  | * #c3 #c4 #Hc3 #Hc4 #H0 destruct
    <path_append_pAbLq_13 in H1; #H1
    <path_append_pAbLq_13 in H2; #H2
    lapply (IH1 … Hc3 … H1 H2) -IH1 -Hc3 #H0 destruct
    <path_append_pAbLq_14 in H1; #H1
    <path_append_pAbLq_14 in H2; #H2
    lapply (IH2 … Hc4 … H1 H2) -IH2 -Hc4 #H0 destruct //
  ]
]
qed-.

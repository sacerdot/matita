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

include "delayed_updating/nederpelt/trab.ma".
include "delayed_updating/syntax/path_balanced_singleton.ma".
include "delayed_updating/syntax/path_structure.ma".
include "ground/generated/prod_3.ma".
include "ground/xoa/ex_3_1.ma".

(* BALANCED SEGMENT TRAVERSAL ***********************************************)

(* Destructions with pbc ****************************************************)

lemma trab_des_gen (p1) (p2) (q1) (q2) (n1) (n2):
      〈p2,n2,q2〉 = ▷𝐛[〈·,·,·〉]❨p1,n1,q1❩ →
      ∃∃r. p2●r = p1 & r●q1 = q2 & (𝗔∗∗n2)●(⊗r)●(𝗟∗∗n1) ϵ 𝐁.
#p1 elim p1 -p1 [| * [ #k1 ] #p1 #IH ] #p2 #q1 #q2 #n1 #n2
[ <trab_unfold_empty #H destruct
  /3 width=4 by pbc_redexes, pbc_empty, ex3_intro/
| #H
  elim (IH … H) -IH -H #r #Hr1 #Hr2 #Hr destruct
  @ex3_intro [| // ] // (**) (* auto fails *)
| #H
  elim (IH … H) -IH -H #r #Hr1 #Hr2 #Hr destruct
  @ex3_intro [| // ] // (**) (* auto fails *)
| #H
  elim (IH … H) -IH -H #r #Hr1 #Hr2
  <list_singleton_succ_rcons <path_append_append_lcons #Hr destruct
  @ex3_intro [| // ] // (**) (* auto fails *)
| @(nat_ind_succ … n1) -n1
  [ <trab_unfold_A_zero #H destruct
    /3 width=4 by pbc_redexes, pbc_empty, ex3_intro/
  | #n1 #_ #H
    elim (IH … H) -IH -H #r #Hr1 #Hr2 #Hr destruct
    @ex3_intro [| // | // ]
    <list_singleton_succ_rcons <path_append_append_lcons
    >list_append_assoc in Hr; #Hr
    lapply (pbc_insert_redex … Hr) -Hr #Hr
    /2 width=1 by pbc_empty, pbc_redex/
  ]
| <trab_unfold_S #H destruct
  /3 width=4 by pbc_redexes, pbc_empty, ex3_intro/
]
qed-.

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

include "delayed_updating/syntax/prototerm.ma".
include "delayed_updating/notation/functions/subset_t_0.ma".

(* PRETERM ******************************************************************)

record preterm_posts (t): Prop ≝
  { term_complete_post (p1) (p2):
(* Note: we cannot extend complete paths *)
      p1 ϵ t → p2 ϵ t → p1 ϵ ↑p2 → p1 = p2
  ; term_root_post (p) (l1) (k2):
(* Note: root paths do not diverge on varible references *)
      p◖l1 ϵ ▵t → p◖𝗱k2 ϵ ▵t → l1 = 𝗱k2
(* Note: applications have arguments *)
  ; term_full_A_post (p):
      p◖𝗔 ϵ ▵t → p◖𝗦 ϵ ▵t
(* application arguments are not empty *)
  ; term_proper_S_post (p):
      p◖𝗦 ϵ t → ⊥
  }.

interpretation
  "preterm (prototerm)"
  'SubsetT = (preterm_posts).

(* Basic destructions *******************************************************)

lemma term_comp_append (t) (p) (q) (n):
      t ϵ 𝐓 → p◖𝗱n ϵ t → p●q ϵ t →
      (𝐞)◖𝗱n = q.
#t #p #q #n #Ht #Hn cases q -q
[| #l #q @(list_ind_rcons … q) -q ]
[ <list_append_empty_sn #Hp
  lapply (term_complete_post … Ht … Hn Hp ?) -t // #H0
  elim (eq_inv_list_lcons_refl ??? H0)
| #Hl
  lapply (term_root_post … Ht p l n ??)
  [ /2 width=1 by term_in_comp_root/
  | /2 width=1 by term_in_comp_root/
  | #H0 destruct //
  ]
| #q #l0 #_ #Hq
  lapply (term_root_post … Ht p l0 n ??)
  [ /2 width=1 by term_in_comp_root/
  | /2 width=2 by term_in_root/
  | #H0 destruct
    lapply (term_complete_post … Ht … Hq Hn ?) -t //
    <list_append_lcons_sn <list_append_rcons_sn >list_append_lcons_sn #H0
    lapply (eq_inv_list_append_dx_dx_refl … (sym_eq … H0)) -p #H0 destruct
  ]
]
qed-.

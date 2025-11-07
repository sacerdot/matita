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

include "delayed_updating/syntax/path_balanced_structure.ma".
include "delayed_updating/syntax/path_beta.ma".

(* PRE REDEX ****************************************************************)

(* Inversions with path_balanced ********************************************)

lemma path_eq_inv_beta_balanced_pSq (p1) (p2) (b1) (q1) (q2) (n1):
      ⊗b1 ϵ 𝐁 →  𝐫❨p1,b1,q1,n1❩ = p2◖𝗦●q2 →
      ∨∨ ∃∃x. p1 = p2◖𝗦●x & 𝐫❨x,b1,q1,n1❩ = q2
       | ∃∃x. 𝐫❨q1,n1❩ = x◖𝗦●q2 & 𝐫❨p1,b1,x❩ = p2
.
#p1 #p2 #b1 #q1 #q2 #n1 #Hb1 <path_beta_unfold_b #H0
elim (path_eq_inv_pbq_pSq_pbc … H0 Hb1) -H0 -Hb1 * #m
[ elim m -m [| #l #x #_ ]
  [ <list_append_empty_sx #H1 #_ destruct
  | <list_append_lcons_sx #H1 #H0
    elim (eq_inv_list_lcons_bi ????? H1) -H1 #H1 #H2 destruct
    >path_beta_unfold_b /3 width=3 by ex2_intro, or_introl/
  ]
| @(list_ind_rcons … m) -m [| #x #l #_ ]
  [ #H0 #_
    elim (eq_inv_list_rcons_bi ????? H0) -H0 #_ #H0 destruct
  | #H1 #H0
    elim (eq_inv_list_rcons_bi ????? (repl_eq … H1 …)) -H1
    [6,7 : // |2,3,4,5: skip ] #H1 #H2 destruct
    >path_p3beta_unfold_b /3 width=3 by ex2_intro, or_intror/
  ]
]
qed-.

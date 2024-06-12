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

include "ground/lib/list_rcons.ma".
include "ground/notation/functions/element_e_0.ma".
include "ground/notation/functions/black_circle_2.ma".
include "ground/notation/functions/black_halfcircleright_2.ma".
include "ground/notation/functions/black_halfcircleleft_2.ma".
include "delayed_updating/syntax/label.ma".
include "delayed_updating/notation/functions/category_p_0.ma".

(* PATH *********************************************************************)

(* Note: a path is a list of labels *)
(* Note: constructed from the leaf (right end) to the root (left end) *)
interpretation
  "path ()"
  'CategoryP = (list label).

interpretation
  "empty (path)"
  'ElementE = (list_empty label).

interpretation
  "right cons (path)"
  'BlackHalfCircleLeft p l = (list_lcons label l p).

interpretation
  "append (path)"
  'BlackCircle p q = (list_append label q p).

interpretation
  "left cons (path)"
  'BlackHalfCircleRight l p = (list_append label p (list_lcons label l (list_empty label))).

(* Basic destructions *******************************************************)

lemma eq_path_dec (p1) (p2):
      Decidable (p1 ={ℙ} p2).
/3 width=1 by eq_label_dec, eq_list_dec/
qed-.

lemma is_path_append_sn_dec (p) (r):
      Decidable (∃q. r = p●q).
#p @(list_ind_rcons … p) -p [| #p #lp #IH ] #r
[ /3 width=3 by ex_intro, or_introl/
| @(list_ind_rcons … r) -r [| #r #lr #_ ]
  [ @or_intror * #q <list_append_rcons_dx
   /2 width=4 by eq_inv_list_empty_rcons/
  | elim (eq_label_dec lp lr) #Hnl destruct
    [ elim (IH r) -IH
      [ * #q #H0 destruct
        /3 width=2 by ex_intro, or_introl/
      | #Hr @or_intror * #q <list_append_rcons_dx #H0
        elim (eq_inv_list_rcons_bi ????? H0) -H0 #H0 #_ destruct
        /3 width=2 by ex_intro/
      ]
    | @or_intror * #q <list_append_rcons_dx #H0
      elim (eq_inv_list_rcons_bi ????? H0) -H0 -IH #_ #H0 destruct
      /2 width=1 by/
    ]
  ]
]
qed-.

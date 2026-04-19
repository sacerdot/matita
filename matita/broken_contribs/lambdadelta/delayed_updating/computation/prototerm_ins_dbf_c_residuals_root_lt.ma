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

include "delayed_updating/reduction/prototerm_dbf_residuals_root_lt.ma".
include "delayed_updating/computation/prototerm_ins_dbf_c_residuals.ma".

(* MEMBERSHIP OF A TRACE TO A SUBSET OF DBF-REDEX POINTERS ******************)

(* Destructions with term_dbfrs and rlt *************************************)

lemma term_in_dbfrs_des_rlt (rs) (y) (u1) (u2):
      y ϵ u1 /𝐝𝐛𝐟 rs → rs ϵ* u2 →
      ∨∨ y ϵ u1 | ∃∃x. x ϵ u2 & ⓪x ⊏ ⓪y.
#rs @(list_ind_rcons … rs) -rs
[ /2 width=1 by or_introl/
| #rs #r #IH #y #u1 #u2 <term_dbfrs_cons_dx #Hy #H0
  elim (term_ins_dbfr_inv_cons_dx … H0) -H0 #Hrs #Hr
  elim (term_in_dbfr_des_rlt … Hy) -Hy #Hy
  [ /2 width=1 by/
  | elim (IH … Hr Hrs) -IH -Hr -Hrs
    [ /3 width=3 by or_intror, ex2_intro/
    | * #x #Hx #Hxr
      /4 width=5 by path_rlt_trans, ex2_intro, or_intror/
    ]
  ]
]
qed-.

lemma term_in_dbfrs_cons_sx_refl_des_rlt (u1) (u2) (r) (rs):
      r ϵ u1 /𝐝𝐛𝐟 (r⨮rs) → rs ϵ* u2 /𝐝𝐛𝐟 r →
      ∃∃x. x ϵ u2 & ⓪x ⊏ ⓪r.
#u1 #u2 #r #rs <term_dbfrs_cons_sx #Hr #Hrs
elim (term_in_dbfrs_des_rlt … Hr Hrs) -Hr -Hrs
[ #Hr elim (term_dbfr_inv_refl_dx … Hr)
| * #x #Hx #Hxr
  elim (term_in_dbfr_des_rlt … Hx) -Hx #Hx
  [ /2 width=3 by ex2_intro/
  | elim (path_rlt_antisym … Hxr Hx)
  ]
]
qed-.

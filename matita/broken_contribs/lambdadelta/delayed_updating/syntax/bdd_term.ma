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

include "delayed_updating/syntax/prototerm_constructors.ma".
include "delayed_updating/syntax/prototerm_eq.ma".
include "delayed_updating/notation/functions/class_d_tau_0.ma".
include "ground/xoa/or_5.ma".
include "ground/xoa/ex_3_1.ma".
include "ground/xoa/ex_4_2.ma".
include "ground/xoa/ex_4_3.ma".
include "ground/xoa/ex_5_3.ma".

(* BY-DEPTH DELAYED (BDD) TERM **********************************************)

inductive bdd: 𝒫❨𝕋❩ ≝
| bdd_oref: ∀k. bdd (⧣k)
| bdd_iref: ∀t,k. bdd t → bdd (𝛕k.t)
| bdd_abst: ∀t. bdd t → bdd (𝛌.t)
| bdd_appl: ∀u,t. bdd u → bdd t → bdd (＠u.t)
| bdd_conv: ∀t1,t2. t1 ⇔ t2 → bdd t1 → bdd t2
.

interpretation
  "by-depth delayed (prototerm)"
  'ClassDTau = (bdd).

(* COMMENT

(* Basic inversions *********************************************************)

lemma bdd_inv_in_comp_gen:
      ∀t,p. t ϵ 𝐃𝛕 → p ϵ t →
      ∨∨ ∃∃n. #n ⇔ t & 𝗱n◗𝐞 = p
       | ∃∃u,q,n. u ϵ 𝐃𝛕 & q ϵ u & 𝛕n.u ⇔ t & 𝗱n◗𝗺◗q = p
       | ∃∃u,q. u ϵ 𝐃𝛕 & q ϵ u & 𝛌.u ⇔ t & 𝗟◗q = p
       | ∃∃v,u,q. v ϵ 𝐃𝛕 & u ϵ 𝐃𝛕 & q ϵ u & @v.u ⇔ t & 𝗔◗q = p
       | ∃∃v,u,q. v ϵ 𝐃𝛕 & u ϵ 𝐃𝛕 & q ϵ v & @v.u ⇔ t & 𝗦◗q = p
.
#t #p #H elim H -H
[ #n * /3 width=3 by or5_intro0, ex2_intro/
| #u #n #Hu #_ * #q #Hq #Hp /3 width=7 by ex4_3_intro, or5_intro1/
| #u #Hu #_ * #q #Hq #Hp /3 width=6 by or5_intro2, ex4_2_intro/
| #v #u #Hv #Hu #_ #_ * * #q #Hq #Hp /3 width=8 by ex5_3_intro, or5_intro3, or5_intro4/
| #t1 #t2 #Ht12 #_ #IH #Ht2
  elim IH -IH [6: /2 width=3 by subset_in_eq_repl_fwd/ ] *
  [ /4 width=3 by subset_eq_trans, or5_intro0, ex2_intro/
  | /4 width=7 by subset_eq_trans, ex4_3_intro, or5_intro1/
  | /4 width=6 by subset_eq_trans, or5_intro2, ex4_2_intro/
  | /4 width=8 by subset_eq_trans, ex5_3_intro, or5_intro3/
  | /4 width=8 by subset_eq_trans, ex5_3_intro, or5_intro4/
  ]
]
qed-.

lemma bdd_inv_in_comp_d:
      ∀t,q,n. t ϵ 𝐃𝛕 → 𝗱n◗q ϵ t →
      ∨∨ ∧∧ #n ⇔ t & 𝐞 = q
       | ∃∃u. u ϵ 𝐃𝛕 & q ϵ ɱ.u & 𝛕n.u ⇔ t
.
#t #q #n #Ht #Hq
elim (bdd_inv_in_comp_gen … Ht Hq) -Ht -Hq *
[ #n0 #H1 #H2 destruct /3 width=1 by or_introl, conj/
| #u0 #q0 #n0 #Hu0 #Hq0 #H1 #H2 destruct
 /4 width=4 by ex3_intro, ex2_intro, or_intror/
| #u0 #q0 #_ #_ #_ #H0 destruct
| #v0 #u0 #q0 #_ #_ #_ #_ #H0 destruct
| #v0 #u0 #q0 #_ #_ #_ #_ #H0 destruct
]
qed-.

lemma bdd_inv_in_root_d:
      ∀t,q,n. t ϵ 𝐃𝛕 → 𝗱n◗q ϵ ▵t →
      ∨∨ ∧∧ #n ⇔ t & 𝐞 = q
       | ∃∃u. u ϵ 𝐃𝛕 & q ϵ ▵ɱ.u & 𝛕n.u ⇔ t
.
#t #q #n #Ht * #r #Hq
elim (bdd_inv_in_comp_d … Ht Hq) -Ht -Hq *
[ #H1 #H2
  elim (eq_inv_list_empty_append … H2) -H2 #H2 #_ destruct
  /3 width=1 by or_introl, conj/
| #u #Hu #Hq #H0 destruct
  /4 width=4 by ex3_intro, ex_intro, or_intror/
]
qed-.

lemma bdd_inv_in_comp_L:
      ∀t,q. t ϵ 𝐃𝛕 → 𝗟◗q ϵ t →
      ∃∃u. u ϵ 𝐃𝛕 & q ϵ u & 𝛌.u ⇔ t
.
#t #q #Ht #Hq
elim (bdd_inv_in_comp_gen … Ht Hq) -Ht -Hq *
[ #n0 #_ #H0 destruct
| #u0 #q0 #n0 #_ #_ #_ #H0 destruct
| #u0 #q0 #Hu0 #Hq0 #H1 #H2 destruct /2 width=4 by ex3_intro/
| #v0 #u0 #q0 #_ #_ #_ #_ #H0 destruct
| #v0 #u0 #q0 #_ #_ #_ #_ #H0 destruct
]
qed-.

lemma bdd_inv_in_root_L:
      ∀t,q. t ϵ 𝐃𝛕 → 𝗟◗q ϵ ▵t →
      ∃∃u. u ϵ 𝐃𝛕 & q ϵ ▵u & 𝛌.u ⇔ t.
#t #q #Ht * #r #Hq
elim (bdd_inv_in_comp_L … Ht Hq) -Ht -Hq
#u #Hu #Hq #H0 destruct
/3 width=4 by ex3_intro, ex_intro/
qed-.

lemma bdd_inv_in_comp_A:
      ∀t,q. t ϵ 𝐃𝛕 → 𝗔◗q ϵ t →
      ∃∃v,u. v ϵ 𝐃𝛕 & u ϵ 𝐃𝛕 & q ϵ u & @v.u ⇔ t
.
#t #q #Ht #Hq
elim (bdd_inv_in_comp_gen … Ht Hq) -Ht -Hq *
[ #n0 #_ #H0 destruct
| #u0 #q0 #n0 #_ #_ #_ #H0 destruct
| #u0 #q0 #_ #_ #_ #H0 destruct
| #v0 #u0 #q0 #Hv0 #Hu0 #Hq0 #H1 #H2 destruct /2 width=6 by ex4_2_intro/
| #v0 #u0 #q0 #_ #_ #_ #_ #H0 destruct
]
qed-.

lemma bdd_inv_in_root_A:
      ∀t,q. t ϵ 𝐃𝛕 → 𝗔◗q ϵ ▵t →
      ∃∃v,u. v ϵ 𝐃𝛕 & u ϵ 𝐃𝛕 & q ϵ ▵u & @v.u ⇔ t
.
#t #q #Ht * #r #Hq
elim (bdd_inv_in_comp_A … Ht Hq) -Ht -Hq
#v #u #Hv #Hu #Hq #H0 destruct
/3 width=6 by ex4_2_intro, ex_intro/
qed-.

lemma bdd_inv_in_comp_S:
      ∀t,q. t ϵ 𝐃𝛕 → 𝗦◗q ϵ t →
      ∃∃v,u. v ϵ 𝐃𝛕 & u ϵ 𝐃𝛕 & q ϵ v & @v.u ⇔ t
.
#t #q #Ht #Hq
elim (bdd_inv_in_comp_gen … Ht Hq) -Ht -Hq *
[ #n0 #_ #H0 destruct
| #u0 #q0 #n0 #_ #_ #_ #H0 destruct
| #u0 #q0 #_ #_ #_ #H0 destruct
| #v0 #u0 #q0 #_ #_ #_ #_ #H0 destruct
| #v0 #u0 #q0 #Hv0 #Hu0 #Hq0 #H1 #H2 destruct /2 width=6 by ex4_2_intro/
]
qed-.

lemma bdd_inv_in_root_S:
      ∀t,q. t ϵ 𝐃𝛕 → 𝗦◗q ϵ ▵t →
      ∃∃v,u. v ϵ 𝐃𝛕 & u ϵ 𝐃𝛕 & q ϵ ▵v & @v.u ⇔ t
.
#t #q #Ht * #r #Hq
elim (bdd_inv_in_comp_S … Ht Hq) -Ht -Hq
#v #u #Hv #Hu #Hq #H0 destruct
/3 width=6 by ex4_2_intro, ex_intro/
qed-.

(* Advanced inversions ******************************************************)

lemma bbd_mono_in_root_d:
      ∀l,n,p,t. t ϵ 𝐃𝛕 → p◖𝗱n ϵ ▵t → p◖l ϵ ▵t → 𝗱n = l.
#l #n #p elim p -p
[ #t #Ht <list_cons_comm <list_cons_comm #Hn #Hl
  elim (bdd_inv_in_root_d … Ht Hn) -Ht -Hn *
  [ #H0 #_
    lapply (prototerm_root_eq_repl … H0) -H0 #H0
    lapply (subset_in_eq_repl_fwd ?? … Hl … H0) -H0 -Hl #Hl
    elim (prototerm_in_root_inv_lcons_oref … Hl) -Hl //
  | #u #_ #_ #H0
    lapply (prototerm_root_eq_repl … H0) -H0 #H0
    lapply (subset_in_eq_repl_fwd ?? … Hl … H0) -H0 -Hl #Hl
    elim (prototerm_in_root_inv_lcons_iref … Hl) -Hl //
  ]
| * [ #m ] #p #IH #t #Ht
  <list_cons_shift <list_cons_shift #Hn #Hl
  [ elim (bdd_inv_in_root_d … Ht Hn) -Ht -Hn *
    [ #_ #H0
      elim (eq_inv_list_empty_rcons ??? H0)
    | #u #Hu #Hp #H0
      lapply (prototerm_root_eq_repl … H0) -H0 #H0
      lapply (subset_in_eq_repl_fwd ?? … Hl … H0) -H0 -Hl #Hl
      elim (prototerm_in_root_inv_lcons_iref … Hl) -Hl #_ #Hl
      /2 width=4 by/
    ]
  | elim (bdd_inv_in_root_L … Ht Hn) -Ht -Hn
    #u #Hu #Hp #H0
    lapply (prototerm_root_eq_repl … H0) -H0 #H0
    lapply (subset_in_eq_repl_fwd ?? … Hl … H0) -H0 -Hl #Hl  
    elim (prototerm_in_root_inv_lcons_abst … Hl) -Hl #_ #Hl
    /2 width=4 by/
  | elim (bdd_inv_in_root_A … Ht Hn) -Ht -Hn
    #v #u #_ #Hu #Hp #H0
    lapply (prototerm_root_eq_repl … H0) -H0 #H0
    lapply (subset_in_eq_repl_fwd ?? … Hl … H0) -H0 -Hl #Hl
    elim (prototerm_in_root_inv_lcons_appl … Hl) -Hl * #H0 #Hl destruct
    /2 width=4 by/
  | elim (bdd_inv_in_root_S … Ht Hn) -Ht -Hn
    #v #u #Hv #_ #Hp #H0
    lapply (prototerm_root_eq_repl … H0) -H0 #H0
    lapply (subset_in_eq_repl_fwd ?? … Hl … H0) -H0 -Hl #Hl
    elim (prototerm_in_root_inv_lcons_appl … Hl) -Hl * #H0 #Hl destruct
    /2 width=4 by/
  ]
]
qed-.
*)

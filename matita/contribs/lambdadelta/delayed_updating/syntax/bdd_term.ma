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

include "ground/xoa/or_5.ma".
include "ground/xoa/ex_3_1.ma".
include "ground/xoa/ex_4_2.ma".
include "ground/xoa/ex_4_3.ma".
include "ground/xoa/ex_5_3.ma".
include "delayed_updating/syntax/term_constructors.ma".
include "delayed_updating/notation/relations/in_predicate_d_phi_1.ma".

(* BY-DEPTH DELAYED (BDD) TERM **********************************************)

inductive bdd: predicate term ≝
| bdd_oref: ∀n. bdd #n
| bdd_iref: ∀t,n. bdd t → bdd 𝛗n.t
| bdd_abst: ∀t. bdd t → bdd 𝛌.t
| bdd_appl: ∀u,t. bdd u → bdd t → bdd @u.t
.

interpretation
  "well-formed by-depth delayed (term)"
  'InPredicateDPhi t = (bdd t).

(* Basic destructions *******************************************************)

lemma bdd_inv_in_com_gen:
      ∀t,p. t ϵ 𝐃𝛗 → p ϵ⬦ t →
      ∨∨ ∃∃n. #n = t & 𝗱❨n❩;𝐞 = p
       | ∃∃u,q,n. u ϵ 𝐃𝛗 & q ϵ⬦ u & 𝛗n.u = t & 𝗱❨n❩;q = p
       | ∃∃u,q. u ϵ 𝐃𝛗 & q ϵ⬦ u & 𝛌.u = t & 𝗟;q = p
       | ∃∃v,u,q. v ϵ 𝐃𝛗 & u ϵ 𝐃𝛗 & q ϵ⬦ u & @v.u = t & 𝗔;q = p
       | ∃∃v,u,q. v ϵ 𝐃𝛗 & u ϵ 𝐃𝛗 & q ϵ⬦ v & @v.u = t & 𝗦;q = p
.
#t #p *
[ #n * /3 width=3 by or5_intro0, ex2_intro/
| #u #n #Hu * #q #Hq #Hp /3 width=7 by ex4_3_intro, or5_intro1/
| #u #Hu * #q #Hq #Hp /3 width=6 by or5_intro2, ex4_2_intro/
| #v #u #Hv #Hu * * #q #Hq #Hp /3 width=8 by ex5_3_intro, or5_intro3, or5_intro4/
]
qed-.

lemma bdd_inv_in_com_d:
      ∀t,q,n. t ϵ 𝐃𝛗 → 𝗱❨n❩;q ϵ⬦ t →
      ∨∨ ∧∧ #n = t & 𝐞 = q
       | ∃∃u. u ϵ 𝐃𝛗 & q ϵ⬦ u & 𝛗n.u = t
.
#t #q #n #Ht #Hq
elim (bdd_inv_in_com_gen … Ht Hq) -Ht -Hq *
[ #n0 #H1 #H2 destruct /3 width=1 by or_introl, conj/
| #u0 #q0 #n0 #Hu0 #Hq0 #H1 #H2 destruct /3 width=4 by ex3_intro, or_intror/
| #u0 #q0 #_ #_ #_ #H0 destruct
| #v0 #u0 #q0 #_ #_ #_ #_ #H0 destruct
| #v0 #u0 #q0 #_ #_ #_ #_ #H0 destruct
]
qed-.

lemma bdd_inv_in_ini_d:
      ∀t,q,n. t ϵ 𝐃𝛗 → 𝗱❨n❩;q ϵ▵ t →
      ∨∨ ∧∧ #n = t & 𝐞 = q
       | ∃∃u. u ϵ 𝐃𝛗 & q ϵ▵ u & 𝛗n.u = t
.
#t #q #n #Ht * #r #Hq
elim (bdd_inv_in_com_d … Ht Hq) -Ht -Hq *
[ #H1 #H2
  elim (eq_inv_list_empty_append … H2) -H2 #H2 #_ destruct
  /3 width=1 by or_introl, conj/
| #u #Hu #Hq #H1 destruct
  /4 width=4 by ex3_intro, ex_intro, or_intror/
]
qed-.

lemma pippo:
      ∀l,n,p,t. t ϵ 𝐃𝛗 → p,𝗱❨n❩ ϵ▵ t → p,l ϵ▵ t → 𝗱❨n❩ = l.
#l #n #p elim p -p
[ #t #Ht <list_cons_comm <list_cons_comm #Hn #Hl
  elim (bdd_inv_in_ini_d … Ht Hn) -Ht -Hn *
  [ #H1 #_ destruct
    elim (term_in_ini_inv_lcons_oref … Hl) -Hl //
  | #u #_ #_ #H1 destruct
    elim (term_in_ini_inv_lcons_iref … Hl) -Hl //
  ]
| * [ #m ] #p #IH #t #Ht
  <list_cons_shift <list_cons_shift #Hn #Hl
  [ elim (bdd_inv_in_ini_d … Ht Hn) -Ht -Hn *
    [ #_ #H
      elim (eq_inv_list_empty_rcons ??? H)
    | #u #Hu #Hp #H destruct
      elim (term_in_ini_inv_lcons_iref … Hl) -Hl #_ #Hl
      @(IH … Hu) //
    ]
  |
  ]
]

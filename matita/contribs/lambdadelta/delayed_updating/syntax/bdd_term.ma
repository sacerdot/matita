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

inductive bdd: π«β¨prototermβ© β
| bdd_oref: βk. bdd (β§£k)
| bdd_iref: βt,k. bdd t β bdd (πk.t)
| bdd_abst: βt. bdd t β bdd (π.t)
| bdd_appl: βu,t. bdd u β bdd t β bdd (οΌ u.t)
| bdd_conv: βt1,t2. t1 β t2 β bdd t1 β bdd t2
.

interpretation
  "by-depth delayed (prototerm)"
  'ClassDTau = (bdd).

(* COMMENT

(* Basic inversions *********************************************************)

lemma bdd_inv_in_comp_gen:
      βt,p. t Ο΅ ππ β p Ο΅ t β
      β¨β¨ ββn. #n β t & π±nβπ = p
       | ββu,q,n. u Ο΅ ππ & q Ο΅ u & πn.u β t & π±nβπΊβq = p
       | ββu,q. u Ο΅ ππ & q Ο΅ u & π.u β t & πβq = p
       | ββv,u,q. v Ο΅ ππ & u Ο΅ ππ & q Ο΅ u & @v.u β t & πβq = p
       | ββv,u,q. v Ο΅ ππ & u Ο΅ ππ & q Ο΅ v & @v.u β t & π¦βq = p
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
      βt,q,n. t Ο΅ ππ β π±nβq Ο΅ t β
      β¨β¨ β§β§ #n β t & π = q
       | ββu. u Ο΅ ππ & q Ο΅ Ι±.u & πn.u β t
.
#t #q #n #Ht #Hq
elim (bdd_inv_in_comp_gen β¦ Ht Hq) -Ht -Hq *
[ #n0 #H1 #H2 destruct /3 width=1 by or_introl, conj/
| #u0 #q0 #n0 #Hu0 #Hq0 #H1 #H2 destruct
 /4 width=4 by ex3_intro, ex2_intro, or_intror/
| #u0 #q0 #_ #_ #_ #H0 destruct
| #v0 #u0 #q0 #_ #_ #_ #_ #H0 destruct
| #v0 #u0 #q0 #_ #_ #_ #_ #H0 destruct
]
qed-.

lemma bdd_inv_in_root_d:
      βt,q,n. t Ο΅ ππ β π±nβq Ο΅ β΅t β
      β¨β¨ β§β§ #n β t & π = q
       | ββu. u Ο΅ ππ & q Ο΅ β΅Ι±.u & πn.u β t
.
#t #q #n #Ht * #r #Hq
elim (bdd_inv_in_comp_d β¦ Ht Hq) -Ht -Hq *
[ #H1 #H2
  elim (eq_inv_list_empty_append β¦ H2) -H2 #H2 #_ destruct
  /3 width=1 by or_introl, conj/
| #u #Hu #Hq #H0 destruct
  /4 width=4 by ex3_intro, ex_intro, or_intror/
]
qed-.

lemma bdd_inv_in_comp_L:
      βt,q. t Ο΅ ππ β πβq Ο΅ t β
      ββu. u Ο΅ ππ & q Ο΅ u & π.u β t
.
#t #q #Ht #Hq
elim (bdd_inv_in_comp_gen β¦ Ht Hq) -Ht -Hq *
[ #n0 #_ #H0 destruct
| #u0 #q0 #n0 #_ #_ #_ #H0 destruct
| #u0 #q0 #Hu0 #Hq0 #H1 #H2 destruct /2 width=4 by ex3_intro/
| #v0 #u0 #q0 #_ #_ #_ #_ #H0 destruct
| #v0 #u0 #q0 #_ #_ #_ #_ #H0 destruct
]
qed-.

lemma bdd_inv_in_root_L:
      βt,q. t Ο΅ ππ β πβq Ο΅ β΅t β
      ββu. u Ο΅ ππ & q Ο΅ β΅u & π.u β t.
#t #q #Ht * #r #Hq
elim (bdd_inv_in_comp_L β¦ Ht Hq) -Ht -Hq
#u #Hu #Hq #H0 destruct
/3 width=4 by ex3_intro, ex_intro/
qed-.

lemma bdd_inv_in_comp_A:
      βt,q. t Ο΅ ππ β πβq Ο΅ t β
      ββv,u. v Ο΅ ππ & u Ο΅ ππ & q Ο΅ u & @v.u β t
.
#t #q #Ht #Hq
elim (bdd_inv_in_comp_gen β¦ Ht Hq) -Ht -Hq *
[ #n0 #_ #H0 destruct
| #u0 #q0 #n0 #_ #_ #_ #H0 destruct
| #u0 #q0 #_ #_ #_ #H0 destruct
| #v0 #u0 #q0 #Hv0 #Hu0 #Hq0 #H1 #H2 destruct /2 width=6 by ex4_2_intro/
| #v0 #u0 #q0 #_ #_ #_ #_ #H0 destruct
]
qed-.

lemma bdd_inv_in_root_A:
      βt,q. t Ο΅ ππ β πβq Ο΅ β΅t β
      ββv,u. v Ο΅ ππ & u Ο΅ ππ & q Ο΅ β΅u & @v.u β t
.
#t #q #Ht * #r #Hq
elim (bdd_inv_in_comp_A β¦ Ht Hq) -Ht -Hq
#v #u #Hv #Hu #Hq #H0 destruct
/3 width=6 by ex4_2_intro, ex_intro/
qed-.

lemma bdd_inv_in_comp_S:
      βt,q. t Ο΅ ππ β π¦βq Ο΅ t β
      ββv,u. v Ο΅ ππ & u Ο΅ ππ & q Ο΅ v & @v.u β t
.
#t #q #Ht #Hq
elim (bdd_inv_in_comp_gen β¦ Ht Hq) -Ht -Hq *
[ #n0 #_ #H0 destruct
| #u0 #q0 #n0 #_ #_ #_ #H0 destruct
| #u0 #q0 #_ #_ #_ #H0 destruct
| #v0 #u0 #q0 #_ #_ #_ #_ #H0 destruct
| #v0 #u0 #q0 #Hv0 #Hu0 #Hq0 #H1 #H2 destruct /2 width=6 by ex4_2_intro/
]
qed-.

lemma bdd_inv_in_root_S:
      βt,q. t Ο΅ ππ β π¦βq Ο΅ β΅t β
      ββv,u. v Ο΅ ππ & u Ο΅ ππ & q Ο΅ β΅v & @v.u β t
.
#t #q #Ht * #r #Hq
elim (bdd_inv_in_comp_S β¦ Ht Hq) -Ht -Hq
#v #u #Hv #Hu #Hq #H0 destruct
/3 width=6 by ex4_2_intro, ex_intro/
qed-.

(* Advanced inversions ******************************************************)

lemma bbd_mono_in_root_d:
      βl,n,p,t. t Ο΅ ππ β pβπ±n Ο΅ β΅t β pβl Ο΅ β΅t β π±n = l.
#l #n #p elim p -p
[ #t #Ht <list_cons_comm <list_cons_comm #Hn #Hl
  elim (bdd_inv_in_root_d β¦ Ht Hn) -Ht -Hn *
  [ #H0 #_
    lapply (prototerm_root_eq_repl β¦ H0) -H0 #H0
    lapply (subset_in_eq_repl_fwd ?? β¦ Hl β¦ H0) -H0 -Hl #Hl
    elim (prototerm_in_root_inv_lcons_oref β¦ Hl) -Hl //
  | #u #_ #_ #H0
    lapply (prototerm_root_eq_repl β¦ H0) -H0 #H0
    lapply (subset_in_eq_repl_fwd ?? β¦ Hl β¦ H0) -H0 -Hl #Hl
    elim (prototerm_in_root_inv_lcons_iref β¦ Hl) -Hl //
  ]
| * [ #m ] #p #IH #t #Ht
  <list_cons_shift <list_cons_shift #Hn #Hl
  [ elim (bdd_inv_in_root_d β¦ Ht Hn) -Ht -Hn *
    [ #_ #H0
      elim (eq_inv_list_empty_rcons ??? H0)
    | #u #Hu #Hp #H0
      lapply (prototerm_root_eq_repl β¦ H0) -H0 #H0
      lapply (subset_in_eq_repl_fwd ?? β¦ Hl β¦ H0) -H0 -Hl #Hl
      elim (prototerm_in_root_inv_lcons_iref β¦ Hl) -Hl #_ #Hl
      /2 width=4 by/
    ]
  | elim (bdd_inv_in_root_L β¦ Ht Hn) -Ht -Hn
    #u #Hu #Hp #H0
    lapply (prototerm_root_eq_repl β¦ H0) -H0 #H0
    lapply (subset_in_eq_repl_fwd ?? β¦ Hl β¦ H0) -H0 -Hl #Hl  
    elim (prototerm_in_root_inv_lcons_abst β¦ Hl) -Hl #_ #Hl
    /2 width=4 by/
  | elim (bdd_inv_in_root_A β¦ Ht Hn) -Ht -Hn
    #v #u #_ #Hu #Hp #H0
    lapply (prototerm_root_eq_repl β¦ H0) -H0 #H0
    lapply (subset_in_eq_repl_fwd ?? β¦ Hl β¦ H0) -H0 -Hl #Hl
    elim (prototerm_in_root_inv_lcons_appl β¦ Hl) -Hl * #H0 #Hl destruct
    /2 width=4 by/
  | elim (bdd_inv_in_root_S β¦ Ht Hn) -Ht -Hn
    #v #u #Hv #_ #Hp #H0
    lapply (prototerm_root_eq_repl β¦ H0) -H0 #H0
    lapply (subset_in_eq_repl_fwd ?? β¦ Hl β¦ H0) -H0 -Hl #Hl
    elim (prototerm_in_root_inv_lcons_appl β¦ Hl) -Hl * #H0 #Hl destruct
    /2 width=4 by/
  ]
]
qed-.
*)

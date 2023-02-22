(**************************************************************************)
(*       ___	                                                            *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||       A.Asperti, C.Sacerdoti Coen,                          *)
(*      ||A||       E.Tassi, S.Zacchiroli                                 *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU Lesser General Public License Version 2.1         *)
(*                                                                        *)
(**************************************************************************)

set "baseuri" "cic:/matita/library_autobatch/nat/exp".

include "auto/nat/div_and_mod.ma".

let rec exp n m on m\def 
 match m with 
 [ O \Rightarrow (S O)
 | (S p) \Rightarrow (times n (exp n p)) ].

interpretation "natural exponent" 'exp a b = (exp a b).

theorem exp_plus_times : \forall n,p,q:nat. 
n \sup (p + q) = (n \sup p) * (n \sup q).
intros.
elim p;simplify;autobatch.
(*[ rewrite < plus_n_O.
  reflexivity
| rewrite > H.
  symmetry.
  apply assoc_times
]*)
qed.

theorem exp_n_O : \forall n:nat. S O = n \sup O.
intro.
autobatch.
(*simplify.
reflexivity.*)
qed.

theorem exp_n_SO : \forall n:nat. n = n \sup (S O).
intro.
autobatch.
(*simplify.
rewrite < times_n_SO.
reflexivity.*)
qed.

theorem exp_exp_times : \forall n,p,q:nat. 
(n \sup p) \sup q = n \sup (p * q).
intros.
elim q;simplify
[ autobatch.
  (*rewrite < times_n_O.
  simplify.
  reflexivity*)
| rewrite > H.
  rewrite < exp_plus_times.
  autobatch
  (*rewrite < times_n_Sm.
  reflexivity*)
]
qed.

theorem lt_O_exp: \forall n,m:nat. O < n \to O < n \sup m. 
intros.
elim m;simplify;autobatch.
                (*unfold lt
[ apply le_n
| rewrite > times_n_SO.
  apply le_times;assumption
]*)
qed.

theorem lt_m_exp_nm: \forall n,m:nat. (S O) < n \to m < n \sup m.
intros.
elim m;simplify;unfold lt;
[ apply le_n.
| apply (trans_le ? ((S(S O))*(S n1)))
  [ simplify.
    rewrite < plus_n_Sm.    
    apply le_S_S.
    autobatch
    (*apply le_S_S.
    rewrite < sym_plus.
    apply le_plus_n*)
  | autobatch
    (*apply le_times;assumption*)
  ]
]
qed.

theorem exp_to_eq_O: \forall n,m:nat. (S O) < n 
\to n \sup m = (S O) \to m = O.
intros.
apply antisym_le
[ apply le_S_S_to_le.
  rewrite < H1.
  autobatch
  (*change with (m < n \sup m).
  apply lt_m_exp_nm.
  assumption*)
| apply le_O_n
]
qed.

theorem injective_exp_r: \forall n:nat. (S O) < n \to 
injective nat nat (\lambda m:nat. n \sup m).
simplify.
intros 4.
apply (nat_elim2 (\lambda x,y.n \sup x = n \sup y \to x = y))
[ intros.
  autobatch
  (*apply sym_eq.
  apply (exp_to_eq_O n)
  [ assumption
  | rewrite < H1.
    reflexivity
  ]*)
| intros.
  apply (exp_to_eq_O n);assumption
| intros.
  apply eq_f.
  apply H1.
  (* esprimere inj_times senza S *)
  cut (\forall a,b:nat.O < n \to n*a=n*b \to a=b)
  [ apply Hcut
    [ autobatch
      (*simplify.
      unfold lt.
      apply le_S_S_to_le. 
      apply le_S. 
      assumption*)
    | (*NB qui autobatch non chiude il goal, chiuso invece chiamando solo la tattica assumption*)
      assumption
    ]
  | intros 2.
    apply (nat_case n);intros;autobatch
    (*[ apply False_ind.
      apply (not_le_Sn_O O H3)
    | apply (inj_times_r m1).
      assumption
    ]*)
  ]
]
qed.

variant inj_exp_r: \forall p:nat. (S O) < p \to \forall n,m:nat.
p \sup n = p \sup m \to n = m \def
injective_exp_r.

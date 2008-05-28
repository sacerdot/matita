(**************************************************************************)
(*       ___	                                                            *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||       A.Asperti, C.Sacerdoti Coen,                          *)
(*      ||A||       E.Tassi, S.Zacchiroli                                 *)
(*      \   /                                                             *)
(*       \ /        Matita is distributed under the terms of the          *)
(*        v         GNU Lesser General Public License Version 2.1         *)
(*                                                                        *)
(**************************************************************************)

set "baseuri" "cic:/matita/library_autobatch/nat/factorization".

include "auto/nat/ord.ma".
include "auto/nat/gcd.ma".
include "auto/nat/nth_prime.ma".

(* the following factorization algorithm looks for the largest prime
   factor. *)
definition max_prime_factor \def \lambda n:nat.
(max n (\lambda p:nat.eqb (n \mod (nth_prime p)) O)).

(* max_prime_factor is indeed a factor *)
theorem divides_max_prime_factor_n:
  \forall n:nat. (S O) < n
  \to nth_prime (max_prime_factor n) \divides n.
intros.
apply divides_b_true_to_divides
[ apply lt_O_nth_prime_n
| apply (f_max_true  (\lambda p:nat.eqb (n \mod (nth_prime p)) O) n);
  cut (\exists i. nth_prime i = smallest_factor n)
  [ elim Hcut.
    apply (ex_intro nat ? a).
    split
    [ apply (trans_le a (nth_prime a))
      [ autobatch
        (*apply le_n_fn.
        exact lt_nth_prime_n_nth_prime_Sn*)
      | rewrite > H1.
        apply le_smallest_factor_n
      ]
    | rewrite > H1.
      (*CSC: simplify here does something nasty! *)
      change with (divides_b (smallest_factor n) n = true).
      apply divides_to_divides_b_true
      [ autobatch
        (*apply (trans_lt ? (S O))
        [ unfold lt.
          apply le_n
        | apply lt_SO_smallest_factor.
          assumption
        ]*)
      | autobatch
        (*letin x \def le.
        autobatch new*)
         (*       
       apply divides_smallest_factor_n;
        apply (trans_lt ? (S O));
        [ unfold lt; apply le_n;
        | assumption; ] *) 
      ] 
    ]
  | autobatch
    (* 
    apply prime_to_nth_prime;
    apply prime_smallest_factor_n;
    assumption; *) 
  ] 
]
qed.

theorem divides_to_max_prime_factor : \forall n,m. (S O) < n \to O < m \to n \divides m \to 
max_prime_factor n \le max_prime_factor m.
intros.
unfold max_prime_factor.
apply f_m_to_le_max
[ autobatch
  (*apply (trans_le ? n)
  [ apply le_max_n
  | apply divides_to_le;assumption
  ]*)
| change with (divides_b (nth_prime (max_prime_factor n)) m = true).
  apply divides_to_divides_b_true
  [ autobatch
    (*cut (prime (nth_prime (max_prime_factor n)))
    [ apply lt_O_nth_prime_n
    | apply prime_nth_prime
    ]*)
  | autobatch
    (*cut (nth_prime (max_prime_factor n) \divides n)
    [ autobatch
    | autobatch
    ] *)   
  (*
    [ apply (transitive_divides ? n);
      [ apply divides_max_prime_factor_n.
        assumption.
      | assumption. 
      ]
    | apply divides_b_true_to_divides;
      [ apply lt_O_nth_prime_n.
      | apply divides_to_divides_b_true;
        [ apply lt_O_nth_prime_n.
        | apply divides_max_prime_factor_n.
          assumption.
        ]
      ]
    ]
  *)
  ]
]  
qed.

theorem p_ord_to_lt_max_prime_factor: \forall n,p,q,r. O < n \to
p = max_prime_factor n \to 
(pair nat nat q r) = p_ord n (nth_prime p) \to
(S O) < r \to max_prime_factor r < p.
intros.
rewrite > H1.
cut (max_prime_factor r \lt max_prime_factor n \lor
    max_prime_factor r = max_prime_factor n)
[ elim Hcut
  [ assumption
  | absurd (nth_prime (max_prime_factor n) \divides r)
    [ rewrite < H4.
      autobatch
      (*apply divides_max_prime_factor_n.
      assumption*)
    | unfold Not.
      intro.
      cut (r \mod (nth_prime (max_prime_factor n)) \neq O)
      [ autobatch
        (*unfold Not in Hcut1.
        autobatch new*)
        (*
        apply Hcut1.apply divides_to_mod_O;
        [ apply lt_O_nth_prime_n.
        | assumption.
        ]
        *)
      | letin z \def le.
        cut(pair nat nat q r=p_ord_aux n n (nth_prime (max_prime_factor n)));
        [ 2: rewrite < H1.
          assumption
        | letin x \def le.
          autobatch width = 4 new
        ]
      (* CERCA COME MAI le_n non lo applica se lo trova come Const e non Rel *)
      ]
      (*  
        apply (p_ord_aux_to_not_mod_O n n ? q r);
        [ apply lt_SO_nth_prime_n.
        | assumption.
        | apply le_n.
        | rewrite < H1.assumption.
        ]
      ].
      *)  
    ]
  ]
| apply (le_to_or_lt_eq (max_prime_factor r)  (max_prime_factor n)).
  apply divides_to_max_prime_factor
  [ assumption
  | assumption
  | apply (witness r n ((nth_prime p) \sup q)).
    rewrite < sym_times.
    apply (p_ord_aux_to_exp n n ? q r)
    [ apply lt_O_nth_prime_n
    | assumption
    ]
  ]
]
qed.

theorem p_ord_to_lt_max_prime_factor1: \forall n,p,q,r. O < n \to
max_prime_factor n \le p \to 
(pair nat nat q r) = p_ord n (nth_prime p) \to
(S O) < r \to max_prime_factor r < p.
intros.
cut (max_prime_factor n < p \lor max_prime_factor n = p)
[ elim Hcut
  [ apply (le_to_lt_to_lt ? (max_prime_factor n))
    [ apply divides_to_max_prime_factor
      [ assumption
      | assumption
      | apply (witness r n ((nth_prime p) \sup q)).
        rewrite > sym_times.
        (*qui autobatch non chiude il goal*)
        apply (p_ord_aux_to_exp n n)
        [ apply lt_O_nth_prime_n.
        | assumption
        ]
      ]
    | assumption
    ]
  | apply (p_ord_to_lt_max_prime_factor n ? q);autobatch
    (*[ assumption
    | apply sym_eq.
      assumption
    | assumption
    | assumption
    ]*)
  ]  
| apply (le_to_or_lt_eq ? p H1)    
]
qed.

(* datatypes and functions *)

inductive nat_fact : Set \def
    nf_last : nat \to nat_fact   
  | nf_cons : nat \to nat_fact \to nat_fact.

inductive nat_fact_all : Set \def
    nfa_zero : nat_fact_all
  | nfa_one : nat_fact_all
  | nfa_proper : nat_fact \to nat_fact_all.

let rec factorize_aux p n acc \def
  match p with 
  [ O \Rightarrow acc
  | (S p1) \Rightarrow 
    match p_ord n (nth_prime p1) with
    [ (pair q r) \Rightarrow 
      factorize_aux p1 r (nf_cons q acc)]].
  
definition factorize : nat \to nat_fact_all \def \lambda n:nat.
  match n with
    [ O \Rightarrow nfa_zero
    | (S n1) \Rightarrow
      match n1 with
      [ O \Rightarrow nfa_one
    | (S n2) \Rightarrow 
      let p \def (max (S(S n2)) (\lambda p:nat.eqb ((S(S n2)) \mod (nth_prime p)) O)) in
      match p_ord (S(S n2)) (nth_prime p) with
      [ (pair q r) \Rightarrow 
           nfa_proper (factorize_aux p r (nf_last (pred q)))]]].
           
let rec defactorize_aux f i \def
  match f with
  [ (nf_last n) \Rightarrow (nth_prime i) \sup (S n)
  | (nf_cons n g) \Rightarrow 
      (nth_prime i) \sup n *(defactorize_aux g (S i))].
      
definition defactorize : nat_fact_all \to nat \def
\lambda f : nat_fact_all. 
match f with 
[ nfa_zero \Rightarrow O
| nfa_one \Rightarrow (S O)
| (nfa_proper g) \Rightarrow defactorize_aux g O]. 

theorem lt_O_defactorize_aux:
 \forall f:nat_fact.
 \forall i:nat.
 O < defactorize_aux f i.
intro.
elim f
[1,2:
  simplify; 
  unfold lt;
  rewrite > times_n_SO;autobatch
  (*apply le_times
  [ change with (O < nth_prime i).
    apply lt_O_nth_prime_n
  |2,3:
    change with (O < exp (nth_prime i) n);
    apply lt_O_exp;
    apply lt_O_nth_prime_n
  | change with (O < defactorize_aux n1 (S i)).
    apply H
  ] *)
]
qed.

theorem lt_SO_defactorize_aux: \forall f:nat_fact.\forall i:nat.
S O < defactorize_aux f i.
intro.
elim f
[ simplify.
  unfold lt.
  rewrite > times_n_SO.
  autobatch
  (*apply le_times
  [ change with (S O < nth_prime i).
    apply lt_SO_nth_prime_n
  | change with (O < exp (nth_prime i) n).
    apply lt_O_exp.
    apply lt_O_nth_prime_n
  ]*)
| simplify.
  unfold lt.
  rewrite > times_n_SO.
  rewrite > sym_times.
  autobatch
  (*apply le_times
  [ change with (O < exp (nth_prime i) n).
    apply lt_O_exp.
    apply lt_O_nth_prime_n
  | change with (S O < defactorize_aux n1 (S i)).
    apply H
  ]*)
]
qed.

theorem defactorize_aux_factorize_aux : 
\forall p,n:nat.\forall acc:nat_fact.O < n \to
((n=(S O) \land p=O) \lor max_prime_factor n < p) \to
defactorize_aux (factorize_aux p n acc) O = n*(defactorize_aux acc p).
intro.
elim p
[ simplify.
  elim H1
  [ elim H2.
    autobatch
    (*rewrite > H3.
    rewrite > sym_times. 
    apply times_n_SO*)
  | apply False_ind.
    apply (not_le_Sn_O (max_prime_factor n) H2)
  ]
| simplify.
  (* generalizing the goal: I guess there exists a better way *)
  cut (\forall q,r.(pair nat nat q r) = (p_ord_aux n1 n1 (nth_prime n)) \to
  defactorize_aux match (p_ord_aux n1 n1 (nth_prime n)) with
  [(pair q r)  \Rightarrow (factorize_aux n r (nf_cons q acc))] O =
  n1*defactorize_aux acc (S n))
  [ (*invocando autobatch in questo punto, dopo circa 7 minuti l'esecuzione non era ancora terminata
      ne' con un errore ne' chiudendo il goal
     *)
    apply (Hcut (fst ? ? (p_ord_aux n1 n1 (nth_prime n)))
    (snd ? ? (p_ord_aux n1 n1 (nth_prime n)))).
    autobatch
    (*apply sym_eq.apply eq_pair_fst_snd*)
  | intros.
    rewrite < H3.
    simplify.
    cut (n1 = r * (nth_prime n) \sup q)
    [ rewrite > H  
      [ simplify.
        autobatch
        (*rewrite < assoc_times.
        rewrite < Hcut.
        reflexivity.*)
      | autobatch
        (*cut (O < r \lor O = r)
        [ elim Hcut1
          [ assumption
          | absurd (n1 = O)
            [ rewrite > Hcut.
              rewrite < H4.
              reflexivity
            | unfold Not.
              intro.
              apply (not_le_Sn_O O).
              rewrite < H5 in \vdash (? ? %).
              assumption
            ]
          ]
        | apply le_to_or_lt_eq.
          apply le_O_n
        ]*)
      | cut ((S O) < r \lor (S O) \nlt r)
        [ elim Hcut1
          [ right.
            apply (p_ord_to_lt_max_prime_factor1 n1 ? q r)
            [ assumption
            | elim H2
              [ elim H5.
                apply False_ind.
                apply (not_eq_O_S n).
                autobatch
                (*apply sym_eq.
                assumption*)
              | autobatch
                (*apply le_S_S_to_le.
                exact H5*)
              ]
            | assumption
            | assumption
            ]
          | cut (r=(S O))
            [ apply (nat_case n)
              [ autobatch
                (*left.
                split
                [ assumption
                | reflexivity
                ]*)
              | intro.
                right.
                rewrite > Hcut2.
                autobatch
                (*simplify.
                unfold lt.
                apply le_S_S.
                apply le_O_n*)
              ]
            | cut (r < (S O) ∨ r=(S O))
              [ elim Hcut2
                [ absurd (O=r)
                  [ autobatch
                    (*apply le_n_O_to_eq.
                    apply le_S_S_to_le.
                    exact H5*)
                  | unfold Not.
                    intro.
                    autobatch
                    (*cut (O=n1)
                    [ apply (not_le_Sn_O O).
                      rewrite > Hcut3 in ⊢ (? ? %).
                      assumption
                    | rewrite > Hcut. 
                      rewrite < H6.
                      reflexivity
                    ]*)
                  ]
                | assumption
                ]
              | autobatch
                (*apply (le_to_or_lt_eq r (S O)).
                apply not_lt_to_le.
                assumption*)
              ]
            ]
          ]
        | apply (decidable_lt (S O) r)
        ]
      ]
    | rewrite > sym_times.
      apply (p_ord_aux_to_exp n1 n1)
      [ apply lt_O_nth_prime_n
      | assumption
      ]
    ]
  ]
]
qed.

theorem defactorize_factorize: \forall n:nat.defactorize (factorize n) = n.
intro.
apply (nat_case n)
[ reflexivity
| intro.
  apply (nat_case m)
  [ reflexivity
  | intro.(*CSC: simplify here does something really nasty *)
    change with  
    (let p \def (max (S(S m1)) (\lambda p:nat.eqb ((S(S m1)) \mod (nth_prime p)) O)) in
    defactorize (match p_ord (S(S m1)) (nth_prime p) with
    [ (pair q r) \Rightarrow 
       nfa_proper (factorize_aux p r (nf_last (pred q)))])=(S(S m1))).
    intro.
    (* generalizing the goal; find a better way *)
    cut (\forall q,r.(pair nat nat q r) = (p_ord (S(S m1)) (nth_prime p)) \to
    defactorize (match p_ord (S(S m1)) (nth_prime p) with
    [ (pair q r) \Rightarrow 
      nfa_proper (factorize_aux p r (nf_last (pred q)))])=(S(S m1)))
    [ (*invocando autobatch qui, dopo circa 300 secondi non si ottiene alcun risultato*)
      apply (Hcut (fst ? ? (p_ord (S(S m1)) (nth_prime p)))
      (snd ? ? (p_ord (S(S m1)) (nth_prime p)))).
      autobatch      
      (*apply sym_eq.
      apply eq_pair_fst_snd*)
    | intros.
      rewrite < H.
      simplify.
      cut ((S(S m1)) = (nth_prime p) \sup q *r)
      [ cut (O<r)
        [ rewrite > defactorize_aux_factorize_aux
          [ (*CSC: simplify here does something really nasty *)
            change with (r*(nth_prime p) \sup (S (pred q)) = (S(S m1))).
            cut ((S (pred q)) = q)
            [ (*invocando autobatch qui, dopo circa 300 secondi non si ottiene ancora alcun risultato*)
              rewrite > Hcut2.
              autobatch
              (*rewrite > sym_times.
              apply sym_eq.
              apply (p_ord_aux_to_exp (S(S m1)))
              [ apply lt_O_nth_prime_n
              | assumption
              ]*)
            | (* O < q *)
              apply sym_eq.
              apply S_pred.
              cut (O < q \lor O = q)
              [ elim Hcut2
                [ assumption              
                | absurd (nth_prime p \divides S (S m1))
                  [ apply (divides_max_prime_factor_n (S (S m1))).
                    autobatch
                    (*unfold lt.
                    apply le_S_S.
                    apply le_S_S.
                    apply le_O_n.*)
                  | cut ((S(S m1)) = r)
                    [ rewrite > Hcut3 in \vdash (? (? ? %)).
                      (*CSC: simplify here does something really nasty *)
                      change with (nth_prime p \divides r \to False).
                      intro.
                      apply (p_ord_aux_to_not_mod_O (S(S m1)) (S(S m1)) (nth_prime p) q r)                      [ apply lt_SO_nth_prime_n
                      | autobatch
                        (*unfold lt.
                        apply le_S_S.
                        apply le_O_n*)
                      | apply le_n
                      | assumption
                      | (*invocando autobatch qui, dopo circa 300 secondi non si ottiene ancora alcun risultato*)
                        apply divides_to_mod_O
                        [ apply lt_O_nth_prime_n
                        | assumption
                        ]
                      ]
                    | rewrite > times_n_SO in \vdash (? ? ? %).
                      rewrite < sym_times.
                      rewrite > (exp_n_O (nth_prime p)).
                      rewrite > H1 in \vdash (? ? ? (? (? ? %) ?)).
                      assumption                      
                    ]
                  ]
                ]
              | autobatch
                (*apply le_to_or_lt_eq.
                apply le_O_n*)
              ]
            ]
          | assumption
          | (* e adesso l'ultimo goal. TASSI: che ora non e' piu' l'ultimo :P *)
            cut ((S O) < r \lor S O \nlt r)
            [ elim Hcut2
              [ right. 
                apply (p_ord_to_lt_max_prime_factor1 (S(S m1)) ? q r);autobatch
                (*[ unfold lt.
                  apply le_S_S. 
                  apply le_O_n
                | apply le_n
                | assumption
                | assumption
                ]*)
              | cut (r=(S O))
                [ apply (nat_case p)
                  [ autobatch
                    (*left.
                    split
                    [ assumption
                    | reflexivity
                    ]*)
                  | intro.
                    right.
                    rewrite > Hcut3.
                    autobatch
                    (*simplify.
                    unfold lt.
                    apply le_S_S.
                    apply le_O_n*)
                  ]
                | cut (r \lt (S O) \or r=(S O))
                  [ elim Hcut3
                    [ absurd (O=r);autobatch
                      (*[ apply le_n_O_to_eq.
                        apply le_S_S_to_le.
                        exact H2
                      | unfold Not.
                        intro.
                        apply (not_le_Sn_O O).
                        rewrite > H3 in \vdash (? ? %).
                        assumption
                      ]*)
                    | assumption
                    ]
                  | autobatch
                    (*apply (le_to_or_lt_eq r (S O)).
                    apply not_lt_to_le.
                    assumption*)
                  ]
                ]
              ]
            | apply (decidable_lt (S O) r)
            ]
          ]
        | (* O < r *)
          cut (O < r \lor O = r)
          [ elim Hcut1
            [ assumption 
            | apply False_ind.
              apply (not_eq_O_S (S m1)).
              rewrite > Hcut.
              rewrite < H1.
              autobatch
              (*rewrite < times_n_O.
              reflexivity*)
            ]
          | autobatch
            (*apply le_to_or_lt_eq.
            apply le_O_n*)  
          ]
        ]
      | (* prova del cut *)
        apply (p_ord_aux_to_exp (S(S m1)));autobatch
        (*[ apply lt_O_nth_prime_n
        | assumption
        ]*)
        (* fine prova cut *)
      ]
    ]
  ]
]
qed.

let rec max_p f \def
match f with
[ (nf_last n) \Rightarrow O
| (nf_cons n g) \Rightarrow S (max_p g)].

let rec max_p_exponent f \def
match f with
[ (nf_last n) \Rightarrow n
| (nf_cons n g) \Rightarrow max_p_exponent g].

theorem divides_max_p_defactorize: \forall f:nat_fact.\forall i:nat. 
nth_prime ((max_p f)+i) \divides defactorize_aux f i.
intro.
elim f
[ simplify.
  autobatch
  (*apply (witness ? ? ((nth_prime i) \sup n)).
  reflexivity*)
| change with 
  (nth_prime (S(max_p n1)+i) \divides
  (nth_prime i) \sup n *(defactorize_aux n1 (S i))).
  elim (H (S i)).
  rewrite > H1.
  rewrite < sym_times.
  rewrite > assoc_times.
  autobatch
  (*rewrite < plus_n_Sm.
  apply (witness ? ? (n2* (nth_prime i) \sup n)).
  reflexivity*)
]
qed.

theorem divides_exp_to_divides: 
\forall p,n,m:nat. prime p \to 
p \divides n \sup m \to p \divides n.
intros 3.
elim m
[ simplify in H1.
  autobatch
  (*apply (transitive_divides p (S O))
  [ assumption
  | apply divides_SO_n
  ]*)
| cut (p \divides n \lor p \divides n \sup n1)
  [ elim Hcut
    [ assumption
    | autobatch
      (*apply H;assumption*)
    ]
  | autobatch
    (*apply divides_times_to_divides
    [ assumption
    | exact H2
    ]*)
  ]
]
qed.

theorem divides_exp_to_eq: 
\forall p,q,m:nat. prime p \to prime q \to
p \divides q \sup m \to p = q.
intros.
unfold prime in H1.
elim H1.
apply H4
[ apply (divides_exp_to_divides p q m);assumption
| (*invocando autobatch in questo punto, dopo piu' di 8 minuti la computazione non
   * era ancora terminata.
   *)
  unfold prime in H.
  (*invocando autobatch anche in questo punto, dopo piu' di 10 minuti la computazione
   * non era ancora terminata.
   *)
  elim H.
  assumption
]
qed.

theorem  not_divides_defactorize_aux: \forall f:nat_fact. \forall i,j:nat.
i < j \to nth_prime i \ndivides defactorize_aux f j.
intro.
elim f
[ change with
  (nth_prime i \divides (nth_prime j) \sup (S n) \to False).
  intro.
  absurd ((nth_prime i) = (nth_prime j))
  [ apply (divides_exp_to_eq ? ? (S n));autobatch
    (*[ apply prime_nth_prime
    | apply prime_nth_prime
    | assumption
    ]*)
  | unfold Not.
    intro.
    cut (i = j)
    [ apply (not_le_Sn_n i).
      rewrite > Hcut in \vdash (? ? %).
      assumption
    | apply (injective_nth_prime ? ? H2)
    ]
  ]
| unfold Not.
  simplify.
  intro.
  cut (nth_prime i \divides (nth_prime j) \sup n
  \lor nth_prime i \divides defactorize_aux n1 (S j))
  [ elim Hcut
    [ absurd ((nth_prime i) = (nth_prime j))
      [ apply (divides_exp_to_eq ? ? n);autobatch
        (*[ apply prime_nth_prime
        | apply prime_nth_prime
        | assumption
        ]*)
      | unfold Not.
        intro.
        cut (i = j)
        [ apply (not_le_Sn_n i).
          rewrite > Hcut1 in \vdash (? ? %).
          assumption
        | apply (injective_nth_prime ? ? H4)
        ]
      ]
    | apply (H i (S j))
      [ autobatch
        (*apply (trans_lt ? j)
        [ assumption
        | unfold lt.
          apply le_n
        ]*)
      | assumption
      ]
    ]
  | autobatch
    (*apply divides_times_to_divides.
    apply prime_nth_prime.
    assumption*)
  ]
]
qed.

lemma not_eq_nf_last_nf_cons: \forall g:nat_fact.\forall n,m,i:nat.
\lnot (defactorize_aux (nf_last n) i= defactorize_aux (nf_cons m g) i).
intros.
change with 
(exp (nth_prime i) (S n) = defactorize_aux (nf_cons m g) i \to False).
intro.
cut (S(max_p g)+i= i)
[ apply (not_le_Sn_n i).
  rewrite < Hcut in \vdash (? ? %). (*chiamando autobatch qui da uno strano errore  "di tipo"*)
  simplify.
  autobatch
  (*apply le_S_S.
  apply le_plus_n*)
| apply injective_nth_prime.
  apply (divides_exp_to_eq ? ? (S n))
  [ apply prime_nth_prime
  | apply prime_nth_prime
  | rewrite > H.
    change with (divides (nth_prime ((max_p (nf_cons m g))+i)) 
    (defactorize_aux (nf_cons m g) i)).
    apply divides_max_p_defactorize
  ]
]
qed.

lemma not_eq_nf_cons_O_nf_cons: \forall f,g:nat_fact.\forall n,i:nat.
\lnot (defactorize_aux (nf_cons O f) i= defactorize_aux (nf_cons (S n) g) i).
intros.
simplify.
unfold Not.
rewrite < plus_n_O.
intro.
apply (not_divides_defactorize_aux f i (S i) ?)
[ autobatch
  (*unfold lt.
  apply le_n*)
| autobatch
  (*rewrite > H.
  rewrite > assoc_times.
  apply (witness ? ? ((exp (nth_prime i) n)*(defactorize_aux g (S i)))).
  reflexivity*)
]
qed.

theorem eq_defactorize_aux_to_eq: \forall f,g:nat_fact.\forall i:nat.
defactorize_aux f i = defactorize_aux g i \to f = g.
intro.
elim f
[ generalize in match H.
  elim g
  [ apply eq_f.
    apply inj_S.
    apply (inj_exp_r (nth_prime i))
    [ apply lt_SO_nth_prime_n
    | (*qui autobatch non conclude il goal attivo*)
      assumption
    ]
  | apply False_ind.
    (*autobatch chiamato qui NON conclude il goal attivo*)
    apply (not_eq_nf_last_nf_cons n2 n n1 i H2)
  ]
| generalize in match H1.
  elim g
  [ apply False_ind.
    apply (not_eq_nf_last_nf_cons n1 n2 n i).
    autobatch
    (*apply sym_eq. 
    assumption*)
  | simplify in H3.
    generalize in match H3.
    apply (nat_elim2 (\lambda n,n2.
    ((nth_prime i) \sup n)*(defactorize_aux n1 (S i)) =
    ((nth_prime i) \sup n2)*(defactorize_aux n3 (S i)) \to
    nf_cons n n1 = nf_cons n2 n3))
    [ intro.
      elim n4
      [ autobatch
        (*apply eq_f.
        apply (H n3 (S i))
        simplify in H4.
        rewrite > plus_n_O.
        rewrite > (plus_n_O (defactorize_aux n3 (S i))).
        assumption*)
      | apply False_ind.
        apply (not_eq_nf_cons_O_nf_cons n1 n3 n5 i).
        (*autobatch chiamato qui NON chiude il goal attivo*)
        assumption
      ]    
    | intros.
      apply False_ind.
      apply (not_eq_nf_cons_O_nf_cons n3 n1 n4 i).      
      apply sym_eq.
      (*autobatch chiamato qui non chiude il goal*)
      assumption
    | intros.
      cut (nf_cons n4 n1 = nf_cons m n3)
      [ cut (n4=m)
        [ cut (n1=n3)
          [ autobatch
            (*rewrite > Hcut1.
            rewrite > Hcut2.
            reflexivity*)
          | change with 
            (match nf_cons n4 n1 with
            [ (nf_last m) \Rightarrow n1
            | (nf_cons m g) \Rightarrow g ] = n3).
            rewrite > Hcut.
            autobatch
            (*simplify.
            reflexivity*)
          ]
        | change with 
          (match nf_cons n4 n1 with
          [ (nf_last m) \Rightarrow m
          | (nf_cons m g) \Rightarrow m ] = m).
          (*invocando autobatch qui, dopo circa 8 minuti la computazione non era ancora terminata*)
          rewrite > Hcut.
          autobatch
          (*simplify.
          reflexivity*)
        ]        
      | apply H4.
        simplify in H5.
        apply (inj_times_r1 (nth_prime i))
        [ apply lt_O_nth_prime_n
        | rewrite < assoc_times.
          rewrite < assoc_times.
          assumption
        ]
      ]
    ]
  ]
]
qed.

theorem injective_defactorize_aux: \forall i:nat.
injective nat_fact nat (\lambda f.defactorize_aux f i).
simplify.
intros.
apply (eq_defactorize_aux_to_eq x y i H).
qed.

theorem injective_defactorize: 
injective nat_fact_all nat defactorize.
unfold injective.
change with (\forall f,g.defactorize f = defactorize g \to f=g).
intro.
elim f
[ generalize in match H.
  elim g
  [ (* zero - zero *)
    reflexivity
  | (* zero - one *)
    simplify in H1.
    apply False_ind.
    apply (not_eq_O_S O H1)
  | (* zero - proper *)
    simplify in H1.
    apply False_ind.
    apply (not_le_Sn_n O).
    rewrite > H1 in \vdash (? ? %).
    autobatch
    (*change with (O < defactorize_aux n O).
    apply lt_O_defactorize_aux*)
  ]
| generalize in match H.
  elim g
  [ (* one - zero *)
    simplify in H1.
    apply False_ind.
    autobatch
    (*apply (not_eq_O_S O).
    apply sym_eq.
    assumption*)
  | (* one - one *)
    reflexivity
  | (* one - proper *)
    simplify in H1.
    apply False_ind.
    apply (not_le_Sn_n (S O)).
    rewrite > H1 in \vdash (? ? %).
    autobatch
    (*change with ((S O) < defactorize_aux n O).
    apply lt_SO_defactorize_aux*)
  ]
| generalize in match H.
  elim g
  [ (* proper - zero *)
    simplify in H1.
    apply False_ind.
    apply (not_le_Sn_n O).
    rewrite < H1 in \vdash (? ? %).
    autobatch
    (*change with (O < defactorize_aux n O).
    apply lt_O_defactorize_aux.*)
  | (* proper - one *)
    simplify in H1.
    apply False_ind.
    apply (not_le_Sn_n (S O)).
    rewrite < H1 in \vdash (? ? %).
    autobatch
    (*change with ((S O) < defactorize_aux n O).
    apply lt_SO_defactorize_aux.*)
  | (* proper - proper *)
    apply eq_f.
    apply (injective_defactorize_aux O).
    (*invocata qui la tattica autobatch NON chiude il goal, chiuso invece 
     *da exact H1
     *)
    exact H1
  ]
]
qed.

theorem factorize_defactorize: 
\forall f,g: nat_fact_all. factorize (defactorize f) = f.
intros.
autobatch.
(*apply injective_defactorize.
apply defactorize_factorize.
*)
qed.

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

include "nat/ord.ma".

(* the following factorization algorithm looks for the largest prime
   factor. *)
definition max_prime_factor \def \lambda n:nat.
(max n (\lambda p:nat.eqb (n \mod (nth_prime p)) O)).

theorem lt_SO_max_prime: \forall m. S O <  m \to 
S O < max m (λi:nat.primeb i∧divides_b i m).
intros.
apply (lt_to_le_to_lt ? (smallest_factor m))
  [apply lt_SO_smallest_factor.assumption
  |apply f_m_to_le_max
    [apply le_smallest_factor_n
    |apply true_to_true_to_andb_true
      [apply prime_to_primeb_true.
       apply prime_smallest_factor_n.
       assumption
      |apply divides_to_divides_b_true
        [apply lt_O_smallest_factor.apply lt_to_le.assumption
        |apply divides_smallest_factor_n.
         apply lt_to_le.assumption
        ]
      ]
    ]
  ]
qed.
(* max_prime_factor is indeed a factor *)
theorem divides_max_prime_factor_n:
  \forall n:nat. (S O) < n
  \to nth_prime (max_prime_factor n) \divides n.
intros.
apply divides_b_true_to_divides.
apply (f_max_true  (\lambda p:nat.eqb (n \mod (nth_prime p)) O) n);
cut (\exists i. nth_prime i = smallest_factor n);
  [ elim Hcut.
    apply (ex_intro nat ? a);
    split;
    [ apply (trans_le a (nth_prime a));
      [ apply le_n_fn;
        exact lt_nth_prime_n_nth_prime_Sn;
      | rewrite > H1;
        apply le_smallest_factor_n; ]
    | rewrite > H1;
      change with (divides_b (smallest_factor n) n = true);
      apply divides_to_divides_b_true;
      [ apply (trans_lt ? (S O));
        [ unfold lt; apply le_n;
        | apply lt_SO_smallest_factor; assumption; ]
      | apply divides_smallest_factor_n;
        autobatch; ] ]
  | apply prime_to_nth_prime;
    autobatch. 
    (* 
    apply prime_to_nth_prime;
    apply prime_smallest_factor_n;
    assumption; *) ] 
qed.

lemma divides_to_prime_divides : \forall n,m.1 < m \to m < n \to m \divides n \to
 \exists p.p \leq m \land prime p \land p \divides n.
intros;apply (ex_intro ? ? (nth_prime (max_prime_factor m)));split
  [split
     [apply divides_to_le
        [apply lt_to_le;assumption
        |apply divides_max_prime_factor_n;assumption]
     |apply prime_nth_prime;]
  |apply (transitive_divides ? ? ? ? H2);apply divides_max_prime_factor_n;
   assumption]
qed.

theorem divides_to_max_prime_factor : \forall n,m. (S O) < n \to O < m \to n \divides m \to 
max_prime_factor n \le max_prime_factor m.
intros.unfold max_prime_factor.
apply f_m_to_le_max.
apply (trans_le ? n).
apply le_max_n.apply divides_to_le.assumption.assumption.
change with (divides_b (nth_prime (max_prime_factor n)) m = true).
apply divides_to_divides_b_true.
cut (prime (nth_prime (max_prime_factor n))).
apply lt_O_nth_prime_n.apply prime_nth_prime.
cut (nth_prime (max_prime_factor n) \divides n).
autobatch.
autobatch.
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
qed.

theorem divides_to_max_prime_factor1 : \forall n,m. O < n \to O < m \to n \divides m \to 
max_prime_factor n \le max_prime_factor m.
intros 3.
elim (le_to_or_lt_eq ? ? H)
  [apply divides_to_max_prime_factor
    [assumption|assumption|assumption]
  |rewrite < H1.
   simplify.apply le_O_n.
  ]
qed.

theorem max_prime_factor_to_not_p_ord_O : \forall n,p,r.
  (S O) < n \to
  p = max_prime_factor n \to
  p_ord n (nth_prime p) \neq pair nat nat O r.
intros.unfold Not.intro.
apply (p_ord_O_to_not_divides ? ? ? ? H2)
  [apply (trans_lt ? (S O))[apply lt_O_S|assumption]
  |rewrite > H1.
   apply divides_max_prime_factor_n.
   assumption
  ]
qed.

theorem p_ord_to_lt_max_prime_factor: \forall n,p,q,r. O < n \to
p = max_prime_factor n \to 
(pair nat nat q r) = p_ord n (nth_prime p) \to
(S O) < r \to max_prime_factor r < p.
intros.
rewrite > H1.
cut (max_prime_factor r \lt max_prime_factor n \lor
    max_prime_factor r = max_prime_factor n).
elim Hcut.assumption.
absurd (nth_prime (max_prime_factor n) \divides r).
rewrite < H4.
apply divides_max_prime_factor_n.
assumption.unfold Not.
intro.
cut (r \mod (nth_prime (max_prime_factor n)) \neq O);
  [ apply Hcut1; autobatch depth=2;
    (*
    apply Hcut1.apply divides_to_mod_O;
    [ apply lt_O_nth_prime_n.
    | assumption.
    ]
    *)
  | unfold p_ord in H2; lapply depth=0 le_n; autobatch width = 4 depth = 2; 
    (*apply (p_ord_aux_to_not_mod_O n n ? q r);
    [ apply lt_SO_nth_prime_n.
    | assumption.
    | apply le_n.
    | rewrite < H1.assumption.
    ]*)
  ].
  
apply (le_to_or_lt_eq (max_prime_factor r)  (max_prime_factor n)).
apply divides_to_max_prime_factor.
assumption.assumption.
apply (witness r n ((nth_prime p) \sup q)).
rewrite < sym_times.
apply (p_ord_aux_to_exp n n ? q r).
apply lt_O_nth_prime_n.assumption.
qed.

theorem p_ord_to_lt_max_prime_factor1: \forall n,p,q,r. O < n \to
max_prime_factor n \le p \to 
(pair nat nat q r) = p_ord n (nth_prime p) \to
(S O) < r \to max_prime_factor r < p.
intros.
cut (max_prime_factor n < p \lor max_prime_factor n = p).
elim Hcut.apply (le_to_lt_to_lt ? (max_prime_factor n)).
apply divides_to_max_prime_factor.assumption.assumption.
apply (witness r n ((nth_prime p) \sup q)).
rewrite > sym_times.
apply (p_ord_aux_to_exp n n).
apply lt_O_nth_prime_n.
assumption.assumption.
apply (p_ord_to_lt_max_prime_factor n ? q).
assumption.apply sym_eq.assumption.assumption.assumption.
apply (le_to_or_lt_eq ? p H1).
qed.

lemma lt_max_prime_factor_to_not_divides: \forall n,p:nat.
O < n \to n=S O \lor max_prime_factor n < p \to 
(nth_prime p \ndivides n).
intros.unfold Not.intro.
elim H1
  [rewrite > H3 in H2.
   apply (le_to_not_lt (nth_prime p) (S O))
    [apply divides_to_le[apply le_n|assumption]
    |apply lt_SO_nth_prime_n
    ]
  |apply (not_le_Sn_n p).
   change with (p < p).
   apply (le_to_lt_to_lt ? ? ? ? H3).
   unfold max_prime_factor.
   apply  f_m_to_le_max
    [apply (trans_le ? (nth_prime p))
      [apply lt_to_le.
       apply lt_n_nth_prime_n
      |apply divides_to_le;assumption
      ]
    |apply eq_to_eqb_true.
     apply divides_to_mod_O
      [apply lt_O_nth_prime_n|assumption]
    ]
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
intro; elim f;
[1,2:
  simplify; unfold lt;
  rewrite > times_n_SO;
  apply le_times;
  [ change with (O < nth_prime i);
    apply lt_O_nth_prime_n;
  |2,3:
    change with (O < exp (nth_prime i) n);
    apply lt_O_exp;
    apply lt_O_nth_prime_n;
  | change with (O < defactorize_aux n1 (S i));
    apply H; ] ]
qed.

theorem lt_SO_defactorize_aux: \forall f:nat_fact.\forall i:nat.
S O < defactorize_aux f i.
intro.elim f.simplify.unfold lt.
rewrite > times_n_SO.
apply le_times.
change with (S O < nth_prime i).
apply lt_SO_nth_prime_n.
change with (O < exp (nth_prime i) n).
apply lt_O_exp.
apply lt_O_nth_prime_n.
simplify.unfold lt.
rewrite > times_n_SO.
rewrite > sym_times.
apply le_times.
change with (O < exp (nth_prime i) n).
apply lt_O_exp.
apply lt_O_nth_prime_n.
change with (S O < defactorize_aux n1 (S i)).
apply H.
qed.

theorem defactorize_aux_factorize_aux : 
\forall p,n:nat.\forall acc:nat_fact.O < n \to
((n=(S O) \land p=O) \lor max_prime_factor n < p) \to
defactorize_aux (factorize_aux p n acc) O = n*(defactorize_aux acc p).
intro.elim p.simplify.
elim H1.elim H2.rewrite > H3.
rewrite > sym_times. apply times_n_SO.
apply False_ind.apply (not_le_Sn_O (max_prime_factor n) H2).
simplify.
(* generalizing the goal: I guess there exists a better way *)
cut (\forall q,r.(pair nat nat q r) = (p_ord_aux n1 n1 (nth_prime n)) \to
defactorize_aux match (p_ord_aux n1 n1 (nth_prime n)) with
[(pair q r)  \Rightarrow (factorize_aux n r (nf_cons q acc))] O =
n1*defactorize_aux acc (S n)).
apply (Hcut (fst ? ? (p_ord_aux n1 n1 (nth_prime n)))
(snd ? ? (p_ord_aux n1 n1 (nth_prime n)))).
apply sym_eq.apply eq_pair_fst_snd.
intros.
rewrite < H3.
simplify.
cut (n1 = r * (nth_prime n) \sup q).
rewrite > H.
simplify.rewrite < assoc_times.
rewrite < Hcut.reflexivity.
cut (O < r \lor O = r).
elim Hcut1.assumption.absurd (n1 = O).
rewrite > Hcut.rewrite < H4.reflexivity.
unfold Not. intro.apply (not_le_Sn_O O).
rewrite < H5 in \vdash (? ? %).assumption.
apply le_to_or_lt_eq.apply le_O_n.
cut ((S O) < r \lor (S O) \nlt r).
elim Hcut1.
right.
apply (p_ord_to_lt_max_prime_factor1 n1 ? q r).
assumption.elim H2.
elim H5.
apply False_ind.
apply (not_eq_O_S n).apply sym_eq.assumption.
apply le_S_S_to_le.
exact H5.
assumption.assumption.
cut (r=(S O)).
apply (nat_case n).
left.split.assumption.reflexivity.
intro.right.rewrite > Hcut2.
simplify.unfold lt.apply le_S_S.apply le_O_n.
cut (r < (S O) ∨ r=(S O)).
elim Hcut2.absurd (O=r).
apply le_n_O_to_eq.apply le_S_S_to_le.exact H5.
unfold Not.intro.
cut (O=n1).
apply (not_le_Sn_O O).
rewrite > Hcut3 in ⊢ (? ? %).
assumption.rewrite > Hcut. 
rewrite < H6.reflexivity.
assumption.
apply (le_to_or_lt_eq r (S O)).
apply not_lt_to_le.assumption.
apply (decidable_lt (S O) r).
rewrite > sym_times.
apply (p_ord_aux_to_exp n1 n1).
apply lt_O_nth_prime_n.assumption.
qed.

theorem defactorize_factorize: \forall n:nat.defactorize (factorize n) = n.
intro.
apply (nat_case n).reflexivity.
intro.apply (nat_case m).reflexivity.
intro.
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
   nfa_proper (factorize_aux p r (nf_last (pred q)))])=(S(S m1))).
apply (Hcut (fst ? ? (p_ord (S(S m1)) (nth_prime p)))
(snd ? ? (p_ord (S(S m1)) (nth_prime p)))).
apply sym_eq.apply eq_pair_fst_snd.
intros.
rewrite < H.
simplify.
cut ((S(S m1)) = (nth_prime p) \sup q *r).
cut (O<r).
rewrite > defactorize_aux_factorize_aux.
change with (r*(nth_prime p) \sup (S (pred q)) = (S(S m1))).
cut ((S (pred q)) = q).
rewrite > Hcut2.
rewrite > sym_times.
apply sym_eq.
apply (p_ord_aux_to_exp (S(S m1))).
apply lt_O_nth_prime_n.
assumption.
(* O < q *)
apply sym_eq. apply S_pred.
cut (O < q \lor O = q).
elim Hcut2.assumption.
absurd (nth_prime p \divides S (S m1)).
apply (divides_max_prime_factor_n (S (S m1))).
unfold lt.apply le_S_S.apply le_S_S. apply le_O_n.
cut ((S(S m1)) = r).
rewrite > Hcut3 in \vdash (? (? ? %)).
change with (nth_prime p \divides r \to False).
intro.
apply (p_ord_aux_to_not_mod_O (S(S m1)) (S(S m1)) (nth_prime p) q r).
apply lt_SO_nth_prime_n.
unfold lt.apply le_S_S.apply le_O_n.apply le_n.
assumption.
apply divides_to_mod_O.apply lt_O_nth_prime_n.assumption.
rewrite > times_n_SO in \vdash (? ? ? %).
rewrite < sym_times.
rewrite > (exp_n_O (nth_prime p)).
rewrite > H1 in \vdash (? ? ? (? (? ? %) ?)).
assumption.
apply le_to_or_lt_eq.apply le_O_n.assumption.
(* e adesso l'ultimo goal. TASSI: che ora non e' piu' l'ultimo :P *)
cut ((S O) < r \lor S O \nlt r).
elim Hcut2.
right. 
apply (p_ord_to_lt_max_prime_factor1 (S(S m1)) ? q r).
unfold lt.apply le_S_S. apply le_O_n.
apply le_n.
assumption.assumption.
cut (r=(S O)).
apply (nat_case p).
left.split.assumption.reflexivity.
intro.right.rewrite > Hcut3.
simplify.unfold lt.apply le_S_S.apply le_O_n.
cut (r \lt (S O) \or r=(S O)).
elim Hcut3.absurd (O=r).
apply le_n_O_to_eq.apply le_S_S_to_le.exact H2.
unfold Not.intro.
apply (not_le_Sn_O O).
rewrite > H3 in \vdash (? ? %).assumption.assumption.
apply (le_to_or_lt_eq r (S O)).
apply not_lt_to_le.assumption.
apply (decidable_lt (S O) r).
(* O < r *)
cut (O < r \lor O = r).
elim Hcut1.assumption. 
apply False_ind.
apply (not_eq_O_S (S m1)).
rewrite > Hcut.rewrite < H1.rewrite < times_n_O.reflexivity.
apply le_to_or_lt_eq.apply le_O_n.
(* prova del cut *)
apply (p_ord_aux_to_exp (S(S m1))).
apply lt_O_nth_prime_n.
assumption.
(* fine prova cut *)
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
elim f.simplify.apply (witness ? ? ((nth_prime i) \sup n)).
reflexivity.
change with 
(nth_prime (S(max_p n1)+i) \divides
(nth_prime i) \sup n *(defactorize_aux n1 (S i))).
elim (H (S i)).
rewrite > H1.
rewrite < sym_times.
rewrite > assoc_times.
rewrite < plus_n_Sm.
apply (witness ? ? (n2* (nth_prime i) \sup n)).
reflexivity.
qed.

lemma eq_p_max: \forall n,p,r:nat. O < n \to
O < r \to
r = (S O) \lor (max r (\lambda p:nat.eqb (r \mod (nth_prime p)) O)) < p \to
p = max_prime_factor (r*(nth_prime p)\sup n).
intros.
apply sym_eq.
unfold max_prime_factor.
apply max_spec_to_max.
split
  [split
    [rewrite > times_n_SO in \vdash (? % ?).
     rewrite > sym_times.
     apply le_times
      [assumption
      |apply lt_to_le.
       apply (lt_to_le_to_lt ? (nth_prime p))
        [apply lt_n_nth_prime_n
        |rewrite > exp_n_SO in \vdash (? % ?).
         apply le_exp
          [apply lt_O_nth_prime_n
          |assumption
          ]
        ]
      ]
    |apply eq_to_eqb_true.
     apply divides_to_mod_O
      [apply lt_O_nth_prime_n
      |apply (lt_O_n_elim ? H).
       intro.
       apply (witness ? ? ((r*(nth_prime p) \sup m))).
       rewrite < assoc_times.
       rewrite < sym_times in \vdash (? ? ? (? % ?)).
       rewrite > exp_n_SO in \vdash (? ? ? (? (? ? %) ?)).
       rewrite > assoc_times.
       rewrite < exp_plus_times.
       reflexivity
      ]
    ]
  |intros.  
   apply not_eq_to_eqb_false.
   unfold Not.intro.
   lapply (mod_O_to_divides ? ? ? H5)
    [apply lt_O_nth_prime_n
    |cut (Not (divides (nth_prime i) ((nth_prime p)\sup n)))
      [elim H2
        [rewrite > H6 in Hletin.
         simplify in Hletin.
         rewrite < plus_n_O in Hletin.
         apply Hcut.assumption
        |elim (divides_times_to_divides ? ? ? ? Hletin)
          [apply (lt_to_not_le ? ? H3).
           apply lt_to_le. 
           apply (le_to_lt_to_lt ? ? ? ? H6).
           apply f_m_to_le_max
            [apply (trans_le ? (nth_prime i))
              [apply lt_to_le.
               apply lt_n_nth_prime_n
              |apply divides_to_le[assumption|assumption]
              ]
            |apply eq_to_eqb_true.
             apply divides_to_mod_O
              [apply lt_O_nth_prime_n|assumption]
            ]
          |apply prime_nth_prime
          |apply Hcut.assumption
          ]
        ]
      |unfold Not.intro.
       apply (lt_to_not_eq ? ? H3).
       apply sym_eq.
       elim (prime_nth_prime p).
       apply injective_nth_prime.
       apply H8
        [apply (divides_exp_to_divides ? ? ? ? H6).
         apply prime_nth_prime.
        |apply lt_SO_nth_prime_n
        ]
      ]
    ]
  ]
qed.

theorem  not_divides_defactorize_aux: \forall f:nat_fact. \forall i,j:nat.
i < j \to nth_prime i \ndivides defactorize_aux f j.
intro.elim f.
change with
(nth_prime i \divides (nth_prime j) \sup (S n) \to False).
intro.absurd ((nth_prime i) = (nth_prime j)).
apply (divides_exp_to_eq ? ? (S n)).
apply prime_nth_prime.apply prime_nth_prime.
assumption.unfold Not.
intro.cut (i = j).
apply (not_le_Sn_n i).rewrite > Hcut in \vdash (? ? %).assumption.
apply (injective_nth_prime ? ? H2).
unfold Not.simplify.
intro.
cut (nth_prime i \divides (nth_prime j) \sup n
\lor nth_prime i \divides defactorize_aux n1 (S j)).
elim Hcut.
absurd ((nth_prime i) = (nth_prime j)).
apply (divides_exp_to_eq ? ? n).
apply prime_nth_prime.apply prime_nth_prime.
assumption.unfold Not.
intro.
cut (i = j).
apply (not_le_Sn_n i).rewrite > Hcut1 in \vdash (? ? %).assumption.
apply (injective_nth_prime ? ? H4).
apply (H i (S j)).
apply (trans_lt ? j).assumption.unfold lt.apply le_n.
assumption.
apply divides_times_to_divides.
apply prime_nth_prime.assumption.
qed.

lemma not_eq_nf_last_nf_cons: \forall g:nat_fact.\forall n,m,i:nat.
\lnot (defactorize_aux (nf_last n) i= defactorize_aux (nf_cons m g) i).
intros.
change with 
(exp (nth_prime i) (S n) = defactorize_aux (nf_cons m g) i \to False).
intro.
cut (S(max_p g)+i= i).
apply (not_le_Sn_n i).
rewrite < Hcut in \vdash (? ? %).
simplify.apply le_S_S.
apply le_plus_n.
apply injective_nth_prime.
apply (divides_exp_to_eq ? ? (S n)).
apply prime_nth_prime.apply prime_nth_prime.
rewrite > H.
change with (divides (nth_prime ((max_p (nf_cons m g))+i)) 
(defactorize_aux (nf_cons m g) i)).
apply divides_max_p_defactorize.
qed.

lemma not_eq_nf_cons_O_nf_cons: \forall f,g:nat_fact.\forall n,i:nat.
\lnot (defactorize_aux (nf_cons O f) i= defactorize_aux (nf_cons (S n) g) i).
intros.
simplify.unfold Not.rewrite < plus_n_O.
intro.
apply (not_divides_defactorize_aux f i (S i) ?).
unfold lt.apply le_n.
rewrite > H.
rewrite > assoc_times.
apply (witness ? ? ((exp (nth_prime i) n)*(defactorize_aux g (S i)))).
reflexivity.
qed.

theorem eq_defactorize_aux_to_eq: \forall f,g:nat_fact.\forall i:nat.
defactorize_aux f i = defactorize_aux g i \to f = g.
intro.
elim f.
elim g in H ⊢ %.
apply eq_f.
apply inj_S. apply (inj_exp_r (nth_prime i)).
apply lt_SO_nth_prime_n.
assumption.
apply False_ind.
apply (not_eq_nf_last_nf_cons n2 n n1 i H1).
elim g in H1 ⊢ %.
apply False_ind.
apply (not_eq_nf_last_nf_cons n1 n2 n i).
apply sym_eq. assumption.
simplify in H2.
generalize in match H2.
apply (nat_elim2 (\lambda n,n2.
((nth_prime i) \sup n)*(defactorize_aux n1 (S i)) =
((nth_prime i) \sup n2)*(defactorize_aux n3 (S i)) \to
nf_cons n n1 = nf_cons n2 n3)).
intro.
elim n4. apply eq_f.
apply (H n3 (S i)).
simplify in H4.
rewrite > plus_n_O.
rewrite > (plus_n_O (defactorize_aux n3 (S i))).assumption.
apply False_ind.
apply (not_eq_nf_cons_O_nf_cons n1 n3 n5 i).assumption.
intros.
apply False_ind.
apply (not_eq_nf_cons_O_nf_cons n3 n1 n4 i).
apply sym_eq.assumption.
intros.
cut (nf_cons n4 n1 = nf_cons m n3).
cut (n4=m).
cut (n1=n3).
rewrite > Hcut1.rewrite > Hcut2.reflexivity.
change with 
(match nf_cons n4 n1 with
[ (nf_last m) \Rightarrow n1
| (nf_cons m g) \Rightarrow g ] = n3).
rewrite > Hcut.simplify.reflexivity.
change with 
(match nf_cons n4 n1 with
[ (nf_last m) \Rightarrow m
| (nf_cons m g) \Rightarrow m ] = m).
rewrite > Hcut.simplify.reflexivity.
apply H3.simplify in H4.
apply (inj_times_r1 (nth_prime i)).
apply lt_O_nth_prime_n.
rewrite < assoc_times.rewrite < assoc_times.assumption.
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
intro.elim f.
elim g in H ⊢ %.
(* zero - zero *)
reflexivity.
(* zero - one *)
simplify in H1.
apply False_ind.
apply (not_eq_O_S O H).
(* zero - proper *)
simplify in H1.
apply False_ind.
apply (not_le_Sn_n O).
rewrite > H in \vdash (? ? %).
change with (O < defactorize_aux n O).
apply lt_O_defactorize_aux.
elim g in H ⊢ %.
(* one - zero *)
simplify in H1.
apply False_ind.
apply (not_eq_O_S O).apply sym_eq. assumption.
(* one - one *)
reflexivity.
(* one - proper *)
simplify in H1.
apply False_ind.
apply (not_le_Sn_n (S O)).
rewrite > H in \vdash (? ? %).
change with ((S O) < defactorize_aux n O).
apply lt_SO_defactorize_aux.
elim g in H ⊢ %.
(* proper - zero *)
simplify in H1.
apply False_ind.
apply (not_le_Sn_n O).
rewrite < H in \vdash (? ? %).
change with (O < defactorize_aux n O).
apply lt_O_defactorize_aux.
(* proper - one *)
simplify in H1.
apply False_ind.
apply (not_le_Sn_n (S O)).
rewrite < H in \vdash (? ? %).
change with ((S O) < defactorize_aux n O).
apply lt_SO_defactorize_aux.
(* proper - proper *)
apply eq_f.
apply (injective_defactorize_aux O).
exact H.
qed.

theorem factorize_defactorize: 
\forall f: nat_fact_all. factorize (defactorize f) = f.
intros.
apply injective_defactorize.
apply defactorize_factorize.
qed.

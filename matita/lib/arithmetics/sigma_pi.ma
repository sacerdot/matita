(*
    ||M||  This file is part of HELM, an Hypertextual, Electronic        
    ||A||  Library of Mathematics, developed at the Computer Science     
    ||T||  Department of the University of Bologna, Italy.                     
    ||I||                                                                 
    ||T||  
    ||A||  This file is distributed under the terms of the 
    \   /  GNU General Public License Version 2        
     \ /      
      V_______________________________________________________________ *)

(* To be ported
include "arithmetics/bigops.ma".

definition natAop ≝ mk_Aop nat 0 plus (λa.refl ? a) (λn.sym_eq ??? (plus_n_O n)) 
   (λa,b,c.sym_eq ??? (associative_plus a b c)).
   
definition natACop ≝ mk_ACop nat 0 natAop commutative_plus.

definition natDop ≝ mk_Dop nat 0 natACop times (λn.(sym_eq ??? (times_n_O n))) 
   distributive_times_plus.

unification hint  0 ≔ ;
   S ≟ natAop
(* ---------------------------------------- *) ⊢ 
   plus ≡ op ? ? S.

unification hint  0 ≔ ;
   S ≟ natACop
(* ---------------------------------------- *) ⊢ 
   plus ≡ op ? ? S.

unification hint  0 ≔ ;
   S ≟ natDop
(* ---------------------------------------- *) ⊢ 
   plus ≡ sum ? ? S.
   
unification hint  0 ≔ ;
   S ≟ natDop
(* ---------------------------------------- *) ⊢ 
   times ≡ prod ? ? S.   
   
(* Sigma e Pi *)

notation "∑_{ ident i < n | p } f"
  with precedence 80
for @{'bigop $n plus 0 (λ${ident i}.$p) (λ${ident i}. $f)}.

notation "∑_{ ident i < n } f"
  with precedence 80
for @{'bigop $n plus 0 (λ${ident i}.true) (λ${ident i}. $f)}.

notation "∑_{ ident j ∈ [a,b[ } f"
  with precedence 80
for @{'bigop ($b-$a) plus 0 (λ${ident j}.((λ${ident j}.true) (${ident j}+$a)))
  (λ${ident j}.((λ${ident j}.$f)(${ident j}+$a)))}.
  
notation "∑_{ ident j ∈ [a,b[ | p } f"
  with precedence 80
for @{'bigop ($b-$a) plus 0 (λ${ident j}.((λ${ident j}.$p) (${ident j}+$a)))
  (λ${ident j}.((λ${ident j}.$f)(${ident j}+$a)))}.
 
notation "∏_{ ident i < n | p} f"
  with precedence 80
for @{'bigop $n times 1 (λ${ident i}.$p) (λ${ident i}. $f)}.
 
notation "∏_{ ident i < n } f"
  with precedence 80
for @{'bigop $n times 1 (λ${ident i}.true) (λ${ident i}. $f)}.

notation "∏_{ ident j ∈ [a,b[ } f"
  with precedence 80
for @{'bigop ($b-$a) times 1 (λ${ident j}.((λ${ident j}.true) (${ident j}+$a)))
  (λ${ident j}.((λ${ident j}.$f)(${ident j}+$a)))}.
  
notation "∏_{ ident j ∈ [a,b[ | p } f"
  with precedence 80
for @{'bigop ($b-$a) times 1 (λ${ident j}.((λ${ident j}.$p) (${ident j}+$a)))
  (λ${ident j}.((λ${ident j}.$f)(${ident j}+$a)))}.

 
(*
    
definition p_ord_times \def
\lambda p,m,x.
  match p_ord x p with
  [pair q r \Rightarrow r*m+q].
  
theorem  eq_p_ord_times: \forall p,m,x.
p_ord_times p m x = (ord_rem x p)*m+(ord x p).
intros.unfold p_ord_times. unfold ord_rem.
unfold ord.
elim (p_ord x p).
reflexivity.
qed.

theorem div_p_ord_times: 
\forall p,m,x. ord x p < m \to p_ord_times p m x / m = ord_rem x p.
intros.rewrite > eq_p_ord_times.
apply div_plus_times.
assumption.
qed.

theorem mod_p_ord_times: 
\forall p,m,x. ord x p < m \to p_ord_times p m x \mod m = ord x p.
intros.rewrite > eq_p_ord_times.
apply mod_plus_times.
assumption.
qed.

lemma lt_times_to_lt_O: \forall i,n,m:nat. i < n*m \to O < m.
intros.
elim (le_to_or_lt_eq O ? (le_O_n m))
  [assumption
  |apply False_ind.
   rewrite < H1 in H.
   rewrite < times_n_O in H.
   apply (not_le_Sn_O ? H)
  ]
qed.

theorem iter_p_gen_knm:
\forall A:Type.
\forall baseA: A.
\forall plusA: A \to A \to A. 
(symmetric A plusA) \to 
(associative A plusA) \to 
(\forall a:A.(plusA a  baseA) = a)\to
\forall g: nat \to A.
\forall h2:nat \to nat \to nat.
\forall h11,h12:nat \to nat. 
\forall k,n,m.
\forall p1,p21:nat \to bool.
\forall p22:nat \to nat \to bool.
(\forall x. x < k \to p1 x = true \to 
p21 (h11 x) = true \land p22 (h11 x) (h12 x) = true
\land h2 (h11 x) (h12 x) = x 
\land (h11 x) < n \land (h12 x) < m) \to
(\forall i,j. i < n \to j < m \to p21 i = true \to p22 i j = true \to 
p1 (h2 i j) = true \land 
h11 (h2 i j) = i \land h12 (h2 i j) = j
\land h2 i j < k) \to
iter_p_gen k p1 A g baseA plusA =
iter_p_gen n p21 A (\lambda x:nat.iter_p_gen m (p22 x) A (\lambda y. g (h2 x y)) baseA plusA) baseA plusA.
intros.
rewrite < (iter_p_gen2' n m p21 p22 ? ? ? ? H H1 H2).
apply sym_eq.
apply (eq_iter_p_gen_gh A baseA plusA H H1 H2 g ? (\lambda x.(h11 x)*m+(h12 x)))
 [intros.
  elim (H4 (i/m) (i \mod m));clear H4
   [elim H7.clear H7.
    elim H4.clear H4.
    assumption
   |apply (lt_times_to_lt_div ? ? ? H5)
   |apply lt_mod_m_m.
    apply (lt_times_to_lt_O ? ? ? H5)
   |apply (andb_true_true ? ? H6)
   |apply (andb_true_true_r ? ? H6)
   ]
 |intros.
  elim (H4 (i/m) (i \mod m));clear H4
   [elim H7.clear H7.
    elim H4.clear H4.
    rewrite > H10.
    rewrite > H9.
    apply sym_eq.
    apply div_mod.
    apply (lt_times_to_lt_O ? ? ? H5)
   |apply (lt_times_to_lt_div ? ? ? H5)
   |apply lt_mod_m_m.
    apply (lt_times_to_lt_O ? ? ? H5)  
   |apply (andb_true_true ? ? H6)
   |apply (andb_true_true_r ? ? H6)
   ]
 |intros.
  elim (H4 (i/m) (i \mod m));clear H4
   [elim H7.clear H7.
    elim H4.clear H4.
    assumption
   |apply (lt_times_to_lt_div ? ? ? H5)
   |apply lt_mod_m_m.
    apply (lt_times_to_lt_O ? ? ? H5)
   |apply (andb_true_true ? ? H6)
   |apply (andb_true_true_r ? ? H6)
   ]
 |intros.
  elim (H3 j H5 H6).
  elim H7.clear H7.
  elim H9.clear H9.
  elim H7.clear H7.
  rewrite > div_plus_times
   [rewrite > mod_plus_times
     [rewrite > H9.
      rewrite > H12.
      reflexivity.
     |assumption
     ]
   |assumption
   ]
 |intros.
  elim (H3 j H5 H6).
  elim H7.clear H7.
  elim H9.clear H9.
  elim H7.clear H7. 
  rewrite > div_plus_times
   [rewrite > mod_plus_times
     [assumption
     |assumption
     ]
   |assumption
   ]
 |intros.
  elim (H3 j H5 H6).
  elim H7.clear H7.
  elim H9.clear H9.
  elim H7.clear H7. 
  apply (lt_to_le_to_lt ? ((h11 j)*m+m))
   [apply monotonic_lt_plus_r.
    assumption
   |rewrite > sym_plus.
    change with ((S (h11 j)*m) \le n*m).
    apply monotonic_le_times_l.
    assumption
   ]
 ]
qed.

theorem iter_p_gen_divides:
\forall A:Type.
\forall baseA: A.
\forall plusA: A \to A \to A. 
\forall n,m,p:nat.O < n \to prime p \to Not (divides p n) \to 
\forall g: nat \to A.
(symmetric A plusA) \to (associative A plusA) \to (\forall a:A.(plusA a  baseA) = a)

\to

iter_p_gen (S (n*(exp p m))) (\lambda x.divides_b x (n*(exp p m))) A g baseA plusA =
iter_p_gen (S n) (\lambda x.divides_b x n) A
  (\lambda x.iter_p_gen (S m) (\lambda y.true) A (\lambda y.g (x*(exp p y))) baseA plusA) baseA plusA.
intros.
cut (O < p)
  [rewrite < (iter_p_gen2 ? ? ? ? ? ? ? ? H3 H4 H5).
   apply (trans_eq ? ? 
    (iter_p_gen (S n*S m) (\lambda x:nat.divides_b (x/S m) n) A
       (\lambda x:nat.g (x/S m*(p)\sup(x\mod S m)))  baseA plusA) )
    [apply sym_eq.
     apply (eq_iter_p_gen_gh ? ? ? ? ? ? g ? (p_ord_times p (S m)))
      [ assumption
      | assumption
      | assumption
      |intros.
       lapply (divides_b_true_to_lt_O ? ? H H7).
       apply divides_to_divides_b_true
        [rewrite > (times_n_O O).
         apply lt_times
          [assumption
          |apply lt_O_exp.assumption
          ]
        |apply divides_times
          [apply divides_b_true_to_divides.assumption
          |apply (witness ? ? (p \sup (m-i \mod (S m)))).
           rewrite < exp_plus_times.
           apply eq_f.
           rewrite > sym_plus.
           apply plus_minus_m_m.
           autobatch by le_S_S_to_le, lt_mod_m_m, lt_O_S;
          ]
        ]
      |intros.
       lapply (divides_b_true_to_lt_O ? ? H H7).
       unfold p_ord_times.
       rewrite > (p_ord_exp1 p ? (i \mod (S m)) (i/S m))
        [change with ((i/S m)*S m+i \mod S m=i).
         apply sym_eq.
         apply div_mod.
         apply lt_O_S
        |assumption
        |unfold Not.intro.
         apply H2.
         apply (trans_divides ? (i/ S m))
          [assumption|
           apply divides_b_true_to_divides;assumption]
        |apply sym_times.
        ]
      |intros.
       apply le_S_S.
       apply le_times
        [apply le_S_S_to_le.
         change with ((i/S m) < S n).
         apply (lt_times_to_lt_l m).
         apply (le_to_lt_to_lt ? i);[2:assumption]
         autobatch by eq_plus_to_le, div_mod, lt_O_S.
        |apply le_exp
          [assumption
          |apply le_S_S_to_le.
           apply lt_mod_m_m.
           apply lt_O_S
          ]
        ]
      |intros.
       cut (ord j p < S m)
        [rewrite > div_p_ord_times
          [apply divides_to_divides_b_true
            [apply lt_O_ord_rem
             [elim H1.assumption
             |apply (divides_b_true_to_lt_O ? ? ? H7).
               rewrite > (times_n_O O).
               apply lt_times
               [assumption|apply lt_O_exp.assumption]
             ]
           |cut (n = ord_rem (n*(exp p m)) p)
              [rewrite > Hcut2.
               apply divides_to_divides_ord_rem
                [apply (divides_b_true_to_lt_O ? ? ? H7).
                 rewrite > (times_n_O O).
                 apply lt_times
                 [assumption|apply lt_O_exp.assumption]
                 |rewrite > (times_n_O O).
                   apply lt_times
                  [assumption|apply lt_O_exp.assumption]
               |assumption
               |apply divides_b_true_to_divides.
                assumption
               ]
              |unfold ord_rem.
              rewrite > (p_ord_exp1 p ? m n)
                [reflexivity
               |assumption
                |assumption
               |apply sym_times
               ]
             ]
            ]
          |assumption
          ]
        |cut (m = ord (n*(exp p m)) p)
          [apply le_S_S.
           rewrite > Hcut1.
           apply divides_to_le_ord
            [apply (divides_b_true_to_lt_O ? ? ? H7).
             rewrite > (times_n_O O).
             apply lt_times
              [assumption|apply lt_O_exp.assumption]
            |rewrite > (times_n_O O).
             apply lt_times
              [assumption|apply lt_O_exp.assumption]
            |assumption
            |apply divides_b_true_to_divides.
             assumption
            ]
          |unfold ord.
           rewrite > (p_ord_exp1 p ? m n)
            [reflexivity
            |assumption
            |assumption
            |apply sym_times
            ]
          ]
        ]
      |intros.
       cut (ord j p < S m)
        [rewrite > div_p_ord_times
          [rewrite > mod_p_ord_times
            [rewrite > sym_times.
             apply sym_eq.
             apply exp_ord
              [elim H1.assumption
              |apply (divides_b_true_to_lt_O ? ? ? H7).
               rewrite > (times_n_O O).
               apply lt_times
                [assumption|apply lt_O_exp.assumption]
              ]
           |cut (m = ord (n*(exp p m)) p)
             [apply le_S_S.
              rewrite > Hcut2.
              apply divides_to_le_ord
               [apply (divides_b_true_to_lt_O ? ? ? H7).
                rewrite > (times_n_O O).
                apply lt_times
                 [assumption|apply lt_O_exp.assumption]
               |rewrite > (times_n_O O).
                apply lt_times
                 [assumption|apply lt_O_exp.assumption]
               |assumption
               |apply divides_b_true_to_divides.
                assumption
               ]
             |unfold ord.
              rewrite > (p_ord_exp1 p ? m n)
                [reflexivity
                |assumption
                |assumption
                |apply sym_times
                ]
              ]
            ]
          |assumption
          ]
        |cut (m = ord (n*(exp p m)) p)
          [apply le_S_S.
           rewrite > Hcut1.
           apply divides_to_le_ord
            [apply (divides_b_true_to_lt_O ? ? ? H7).
             rewrite > (times_n_O O).
             apply lt_times
              [assumption|apply lt_O_exp.assumption]
            |rewrite > (times_n_O O).
             apply lt_times
              [assumption|apply lt_O_exp.assumption]
            |assumption
            |apply divides_b_true_to_divides.
             assumption
            ]
          |unfold ord.
           rewrite > (p_ord_exp1 p ? m n)
            [reflexivity
            |assumption
            |assumption
            |apply sym_times
            ]
          ]
        ]
      |intros.
       rewrite > eq_p_ord_times.
       rewrite > sym_plus.
       apply (lt_to_le_to_lt ? (S m +ord_rem j p*S m))
        [apply lt_plus_l.
         apply le_S_S.
         cut (m = ord (n*(p \sup m)) p)
          [rewrite > Hcut1.
           apply divides_to_le_ord
            [apply (divides_b_true_to_lt_O ? ? ? H7).
             rewrite > (times_n_O O).
             apply lt_times
              [assumption|apply lt_O_exp.assumption]
            |rewrite > (times_n_O O).
             apply lt_times
              [assumption|apply lt_O_exp.assumption]
            |assumption
            |apply divides_b_true_to_divides.
             assumption
            ]
          |unfold ord.
           rewrite > sym_times.
           rewrite > (p_ord_exp1 p ? m n)
            [reflexivity
            |assumption
            |assumption
            |reflexivity
            ]
          ]
        |change with (S (ord_rem j p)*S m \le S n*S m).
         apply le_times_l.
         apply le_S_S.
         cut (n = ord_rem (n*(p \sup m)) p)
          [rewrite > Hcut1.
           apply divides_to_le
            [apply lt_O_ord_rem
              [elim H1.assumption
              |rewrite > (times_n_O O).
               apply lt_times
                [assumption|apply lt_O_exp.assumption]
              ]
            |apply divides_to_divides_ord_rem
              [apply (divides_b_true_to_lt_O ? ? ? H7).
               rewrite > (times_n_O O).
               apply lt_times
                [assumption|apply lt_O_exp.assumption]
              |rewrite > (times_n_O O).
               apply lt_times
                [assumption|apply lt_O_exp.assumption]
              |assumption
              |apply divides_b_true_to_divides.
               assumption
              ]
            ]
        |unfold ord_rem.
         rewrite > sym_times.
         rewrite > (p_ord_exp1 p ? m n)
          [reflexivity
          |assumption
          |assumption
          |reflexivity
          ]
        ]
      ]
    ]
  |apply eq_iter_p_gen
  
    [intros.
     elim (divides_b (x/S m) n);reflexivity
    |intros.reflexivity
    ]
  ]
|elim H1.apply lt_to_le.assumption
]
qed.
    


theorem iter_p_gen_2_eq: 
\forall A:Type.
\forall baseA: A.
\forall plusA: A \to A \to A. 
(symmetric A plusA) \to 
(associative A plusA) \to 
(\forall a:A.(plusA a  baseA) = a)\to
\forall g: nat \to nat \to A.
\forall h11,h12,h21,h22: nat \to nat \to nat. 
\forall n1,m1,n2,m2.
\forall p11,p21:nat \to bool.
\forall p12,p22:nat \to nat \to bool.
(\forall i,j. i < n2 \to j < m2 \to p21 i = true \to p22 i j = true \to 
p11 (h11 i j) = true \land p12 (h11 i j) (h12 i j) = true
\land h21 (h11 i j) (h12 i j) = i \land h22 (h11 i j) (h12 i j) = j
\land h11 i j < n1 \land h12 i j < m1) \to
(\forall i,j. i < n1 \to j < m1 \to p11 i = true \to p12 i j = true \to 
p21 (h21 i j) = true \land p22 (h21 i j) (h22 i j) = true
\land h11 (h21 i j) (h22 i j) = i \land h12 (h21 i j) (h22 i j) = j
\land (h21 i j) < n2 \land (h22 i j) < m2) \to
iter_p_gen n1 p11 A 
     (\lambda x:nat .iter_p_gen m1 (p12 x) A (\lambda y. g x y) baseA plusA) 
     baseA plusA =
iter_p_gen n2 p21 A 
    (\lambda x:nat .iter_p_gen m2 (p22 x) A  (\lambda y. g (h11 x y) (h12 x y)) baseA plusA )
    baseA plusA.

intros.
rewrite < (iter_p_gen2' ? ? ? ? ? ? ? ? H H1 H2).
letin ha:= (\lambda x,y.(((h11 x y)*m1) + (h12 x y))).
letin ha12:= (\lambda x.(h21 (x/m1) (x \mod m1))).
letin ha22:= (\lambda x.(h22 (x/m1) (x \mod m1))).

apply (trans_eq ? ? 
(iter_p_gen n2 p21 A (\lambda x:nat. iter_p_gen m2 (p22 x) A
 (\lambda y:nat.(g (((h11 x y)*m1+(h12 x y))/m1) (((h11 x y)*m1+(h12 x y))\mod m1))) baseA plusA ) baseA plusA))
[
  apply (iter_p_gen_knm A baseA plusA H H1 H2 (\lambda e. (g (e/m1) (e \mod m1))) ha ha12 ha22);intros
  [ elim (and_true ? ? H6).
    cut(O \lt m1)
    [ cut(x/m1 < n1)
      [ cut((x \mod m1) < m1)
        [ elim (H4 ? ? Hcut1 Hcut2 H7 H8).
          elim H9.clear H9.
          elim H11.clear H11.
          elim H9.clear H9.
          elim H11.clear H11.
          split
          [ split
            [ split
              [ split
                [ assumption
                | assumption
                ]
              | unfold ha.
                unfold ha12.
                unfold ha22.
                rewrite > H14.
                rewrite > H13.
                apply sym_eq.
                apply div_mod.
                assumption
              ]
            | assumption
            ]
          | assumption
          ]
        | apply lt_mod_m_m.
          assumption
        ]
      | apply (lt_times_n_to_lt m1)
        [ assumption
        | apply (le_to_lt_to_lt ? x)
          [ apply (eq_plus_to_le ? ? (x \mod m1)).
            apply div_mod.
            assumption
          | assumption
        ]
      ]  
    ]
    | apply not_le_to_lt.unfold.intro.
      generalize in match H5.
      apply (le_n_O_elim ? H9).
      rewrite < times_n_O.
      apply le_to_not_lt.
      apply le_O_n.              
    ]
  | elim (H3 ? ? H5 H6 H7 H8).
    elim H9.clear H9.
    elim H11.clear H11.
    elim H9.clear H9.
    elim H11.clear H11.
    cut(((h11 i j)*m1 + (h12 i j))/m1 = (h11 i j))
    [ cut(((h11 i j)*m1 + (h12 i j)) \mod m1 = (h12 i j))
      [ split
        [ split
          [ split
            [ apply true_to_true_to_andb_true
              [ rewrite > Hcut.
                assumption
              | rewrite > Hcut1.
                rewrite > Hcut.
                assumption
              ] 
            | unfold ha.
              unfold ha12.
              rewrite > Hcut1.
              rewrite > Hcut.
              assumption
            ]
          | unfold ha.
            unfold ha22.
            rewrite > Hcut1.
            rewrite > Hcut.
            assumption            
          ]
        | cut(O \lt m1)
          [ cut(O \lt n1)      
            [ apply (lt_to_le_to_lt ? ((h11 i j)*m1 + m1) )
              [ unfold ha.
                apply (lt_plus_r).
                assumption
              | rewrite > sym_plus.
                rewrite > (sym_times (h11 i j) m1).
                rewrite > times_n_Sm.
                rewrite > sym_times.
                apply (le_times_l).
                assumption  
              ]
            | apply not_le_to_lt.unfold.intro.
              generalize in match H12.
              apply (le_n_O_elim ? H11).       
              apply le_to_not_lt.
              apply le_O_n
            ]
          | apply not_le_to_lt.unfold.intro.
            generalize in match H10.
            apply (le_n_O_elim ? H11).       
            apply le_to_not_lt.
            apply le_O_n
          ]  
        ]
      | rewrite > (mod_plus_times m1 (h11 i j) (h12 i j)).
        reflexivity.
        assumption
      ]     
    | rewrite > (div_plus_times m1 (h11 i j) (h12 i j)).
      reflexivity.
      assumption
    ]
  ]
| apply (eq_iter_p_gen1)
  [ intros. reflexivity 
  | intros.
    apply (eq_iter_p_gen1)
    [ intros. reflexivity
    | intros.
      rewrite > (div_plus_times)
      [ rewrite > (mod_plus_times)
        [ reflexivity
        | elim (H3 x x1 H5 H7 H6 H8).
          assumption
        ]
      | elim (H3 x x1 H5 H7 H6 H8).       
        assumption
      ]
    ]
  ]
]
qed.

theorem iter_p_gen_iter_p_gen: 
\forall A:Type.
\forall baseA: A.
\forall plusA: A \to A \to A. 
(symmetric A plusA) \to 
(associative A plusA) \to 
(\forall a:A.(plusA a  baseA) = a)\to
\forall g: nat \to nat \to A.
\forall n,m.
\forall p11,p21:nat \to bool.
\forall p12,p22:nat \to nat \to bool.
(\forall x,y. x < n \to y < m \to 
 (p11 x \land p12 x y) = (p21 y \land p22 y x)) \to
iter_p_gen n p11 A 
  (\lambda x:nat.iter_p_gen m (p12 x) A (\lambda y. g x y) baseA plusA) 
  baseA plusA =
iter_p_gen m p21 A 
  (\lambda y:nat.iter_p_gen n (p22 y) A  (\lambda x. g x y) baseA plusA )
  baseA plusA.
intros.
apply (iter_p_gen_2_eq A baseA plusA H H1 H2 (\lambda x,y. g x y) (\lambda x,y.y) (\lambda x,y.x) (\lambda x,y.y) (\lambda x,y.x)
       n m m n p11 p21 p12 p22)
  [intros.split
    [split
      [split
        [split
          [split
            [apply (andb_true_true ? (p12 j i)).
             rewrite > H3
              [rewrite > H6.rewrite > H7.reflexivity
              |assumption
              |assumption
              ]
            |apply (andb_true_true_r (p11 j)).
             rewrite > H3
              [rewrite > H6.rewrite > H7.reflexivity
              |assumption
              |assumption
              ]
            ]
          |reflexivity
          ]
        |reflexivity
        ]
      |assumption
      ]
    |assumption
    ]
  |intros.split
    [split
      [split
        [split
          [split
            [apply (andb_true_true ? (p22 j i)).
             rewrite < H3
              [rewrite > H6.rewrite > H7.reflexivity
              |assumption
              |assumption
              ]
            |apply (andb_true_true_r (p21 j)).
             rewrite < H3
              [rewrite > H6.rewrite > H7.reflexivity
              |assumption
              |assumption
              ]
            ]
          |reflexivity
          ]
        |reflexivity
        ]
      |assumption
      ]
    |assumption
    ]
  ]
qed. *)*)
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

include "Q/q/qinv.ma".
include "Q/ratio/rtimes.ma".

definition Qtimes : Q \to Q \to Q \def
\lambda p,q.
  match p with
  [OQ \Rightarrow OQ
  |Qpos p1 \Rightarrow 
    match q with
    [OQ \Rightarrow OQ
    |Qpos q1 \Rightarrow Qpos (rtimes p1 q1)
    |Qneg q1 \Rightarrow Qneg (rtimes p1 q1)
    ]
  |Qneg p1 \Rightarrow 
    match q with
    [OQ \Rightarrow OQ
    |Qpos q1 \Rightarrow Qneg (rtimes p1 q1)
    |Qneg q1 \Rightarrow Qpos (rtimes p1 q1)
    ]
  ].

interpretation "rational times" 'times x y = (Qtimes x y).

theorem Qtimes_q_OQ: ∀q. q * OQ = OQ.
 intro;
 elim q;
 reflexivity.
qed.

theorem symmetric_Qtimes: symmetric ? Qtimes.
 intros 2;
 elim x;
  [ rewrite > Qtimes_q_OQ; reflexivity 
  |*:elim y;
     simplify;
     try rewrite > sym_rtimes;
     reflexivity
  ]
qed.

theorem Qtimes_q_Qone: ∀q.q * Qone = q.
 intro.cases q
  [reflexivity
  |2,3: cases r; reflexivity
  ]
qed.

theorem Qtimes_Qone_q: ∀q.Qone * q = q.
 intro.cases q
  [reflexivity
  |2,3: cases r; reflexivity
  ]
qed.

theorem Qtimes_Qinv: ∀q. q ≠ OQ → q * (Qinv q) = Qpos one.
 intro;
 elim q;
  [ elim H; reflexivity
  |*:simplify;
     rewrite > rtimes_rinv;
     reflexivity
  ]
qed.

theorem times_fa_Qtimes: \forall f,g. nat_fact_all_to_Q (times_fa f g) =
Qtimes (nat_fact_all_to_Q f) (nat_fact_all_to_Q g).
intros.
cases f;simplify
  [reflexivity
  |cases g;reflexivity
  |cases g;simplify
    [reflexivity
    |reflexivity
    |rewrite > times_f_ftimes.reflexivity]]
qed.

theorem times_Qtimes: \forall p,q.
(nat_to_Q (p*q)) = Qtimes (nat_to_Q p) (nat_to_Q q).
intros.unfold nat_to_Q.
rewrite < times_fa_Qtimes.
rewrite < eq_times_times_fa.
reflexivity.
qed.

theorem associative_Qtimes:associative ? Qtimes.
unfold.intros.
cases x
  [reflexivity
   (* non posso scrivere 2,3: ... ?? *)
  |cases y
    [reflexivity.
    |cases z
      [reflexivity
      |simplify.rewrite > associative_rtimes.
       reflexivity.
      |simplify.rewrite > associative_rtimes.
       reflexivity
      ]
    |cases z
      [reflexivity
      |simplify.rewrite > associative_rtimes.
       reflexivity.
      |simplify.rewrite > associative_rtimes.
       reflexivity
      ]
    ]
  |cases y
    [reflexivity.
    |cases z
      [reflexivity
      |simplify.rewrite > associative_rtimes.
       reflexivity.
      |simplify.rewrite > associative_rtimes.
       reflexivity
      ]
    |cases z
      [reflexivity
      |simplify.rewrite > associative_rtimes.
       reflexivity.
      |simplify.rewrite > associative_rtimes.
       reflexivity]]]
qed.

theorem eq_Qtimes_OQ_to_eq_OQ: \forall p,q.
Qtimes p q = OQ \to p = OQ \lor q = OQ.
intros 2.
cases p
  [intro.left.reflexivity
  |cases q
    [intro.right.reflexivity
    |simplify.intro.destruct H
    |simplify.intro.destruct H
    ]
  |cases q
    [intro.right.reflexivity
    |simplify.intro.destruct H
    |simplify.intro.destruct H]]
qed.

theorem Qinv_Qtimes: \forall p,q.
p \neq OQ \to q \neq OQ \to Qinv(Qtimes p q) = Qtimes (Qinv p) (Qinv q).
intros.
rewrite < Qtimes_Qone_q in ⊢ (? ? ? %).
rewrite < (Qtimes_Qinv (Qtimes p q))
  [lapply (Qtimes_Qinv ? H).
   lapply (Qtimes_Qinv ? H1).
   rewrite > symmetric_Qtimes in ⊢ (? ? ? (? % ?)).
   rewrite > associative_Qtimes.
   rewrite > associative_Qtimes.
   rewrite < associative_Qtimes in ⊢ (? ? ? (? ? (? ? %))).
   rewrite < symmetric_Qtimes in ⊢ (? ? ? (? ? (? ? (? % ?)))).
   rewrite > associative_Qtimes in ⊢ (? ? ? (? ? (? ? %))).
   rewrite > Hletin1.
   rewrite > Qtimes_q_Qone.
   rewrite > Hletin.
   rewrite > Qtimes_q_Qone.
   reflexivity
  |intro.
   elim (eq_Qtimes_OQ_to_eq_OQ ? ? H2)
    [apply (H H3)|apply (H1 H3)]]
qed.

(* a stronger version, taking advantage of inv(O) = O *)
theorem Qinv_Qtimes': \forall p,q. Qinv(Qtimes p q) = Qtimes (Qinv p) (Qinv q).
intros.
cases p
  [reflexivity
  |cases q
    [reflexivity
    |apply Qinv_Qtimes;intro;destruct H
    |apply Qinv_Qtimes;intro;destruct H
    ]
  |cases q
    [reflexivity
    |apply Qinv_Qtimes;intro;destruct H
    |apply Qinv_Qtimes;intro;destruct H]]
qed.

theorem Qtimes_numerator_denominator: ∀f:fraction.
  Qtimes (nat_fact_all_to_Q (numerator f)) (Qinv (nat_fact_all_to_Q (denominator f)))
  = Qpos (frac f).
simplify.
intro.elim f
  [reflexivity
  |reflexivity
  |elim (or_numerator_nfa_one_nfa_proper f1)
    [elim H1.clear H1.
     elim H3.clear H3.
     cut (finv (nat_fact_to_fraction a) = f1)
      [elim z;
       simplify;
       rewrite > H2;rewrite > H1;simplify;
       rewrite > Hcut;reflexivity
      |generalize in match H.
       rewrite > H2.rewrite > H1.simplify.
       intro.destruct H3.reflexivity
      ]
    |elim H1;clear H1;
     elim z
      [*:simplify;
       rewrite > H2;simplify;
       elim (or_numerator_nfa_one_nfa_proper (finv f1))
        [1,3,5:elim H1;clear H1;
         rewrite > H3;simplify;
         cut (nat_fact_to_fraction a = f1)
          [1,3,5:rewrite > Hcut;reflexivity
          |*:generalize in match H;
           rewrite > H2;
           rewrite > H3;
           rewrite > Qtimes_q_Qone;
           intro;
           simplify in H1;
           destruct H1;
           reflexivity
          ]
        |*:elim H1;clear H1;
         generalize in match H;
         rewrite > H2;
         rewrite > H3;simplify;
         intro;
         destruct H1;
         rewrite > Hcut;
         simplify;reflexivity
        ]]]]
qed.



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



include "nat/div_and_mod.ma".
include "nat/primes.ma".
include "list/list.ma".

axiom mod_plus: ∀a,b,m. (a + b) \mod m = (a \mod m + b \mod m) \mod m.
axiom mod_mod: ∀a,n,m. n∣m → a \mod n = a \mod n \mod m.
axiom eq_mod_times_n_m_m_O: ∀n,m. O < m → n * m \mod m = O.
axiom eq_mod_to_eq_plus_mod: ∀a,b,c,m. a \mod m = b \mod m → (a+c) \mod m = (b+c) \mod m.
axiom eq_mod_times_times_mod: ∀a,b,n,m. m = a*n → (a*b) \mod m = a * (b \mod n).
axiom divides_to_eq_mod_mod_mod: ∀a,n,m. n∣m → a \mod m \mod n = a \mod n.
axiom le_to_le_plus_to_le : ∀a,b,c,d.b\leq d\rarr a+b\leq c+d\rarr a\leq c.
axiom or_lt_le : ∀n,m. n < m ∨ m ≤ n.

inductive cartesian_product (A,B: Type) : Type ≝
 couple: ∀a:A.∀b:B. cartesian_product A B.

lemma le_to_lt: ∀n,m. n ≤ m → n < S m.
 intros;
 autobatch.
qed.

alias num (instance 0) = "natural number".
definition nat_of_bool ≝
 λb. match b with [ true ⇒ 1 | false ⇒ 0 ].

theorem lt_trans: ∀x,y,z. x < y → y < z → x < z.
 unfold lt;
 intros;
 autobatch.
qed.

lemma leq_m_n_to_eq_div_n_m_S: ∀n,m:nat. 0 < m → m ≤ n → ∃z. n/m = S z.
 intros;
 unfold div;
 apply (ex_intro ? ? (div_aux (pred n) (n-m) (pred m)));
 cut (∃w.m = S w);
  [ elim Hcut;
    rewrite > H2;
    rewrite > H2 in H1;
    clear Hcut; clear H2; clear H; (*clear m;*)
    simplify;
    unfold in ⊢ (? ? % ?);
    cut (∃z.n = S z);
     [ elim Hcut; clear Hcut;
       rewrite > H in H1;
       rewrite > H; clear m;
       change in ⊢ (? ? % ?)  with
        (match leb (S a1) a with
         [ true ⇒ O
         | false ⇒ S (div_aux a1 ((S a1) - S a) a)]);
       cut (S a1 ≰ a);
        [ apply (leb_elim (S a1) a);
           [ intro;
             elim (Hcut H2)
           | intro;
             simplify;
             reflexivity
           ]
        | intro;
          autobatch
        ]
     | elim H1; autobatch
     ]
  | autobatch
  ].
qed.

axiom daemon: False.

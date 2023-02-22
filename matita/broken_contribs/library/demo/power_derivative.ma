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

include "nat/plus.ma".
include "nat/orders.ma".
include "nat/compare.ma".

axiom R: Type.
axiom R0: R.
axiom R1: R.
axiom Rplus: R→R→R.
axiom Rmult: R→R→R.

notation "0" with precedence 89
for @{ 'zero }.
interpretation "Rzero" 'zero = (R0).
interpretation "Nzero" 'zero = (O).

notation "1" with precedence 89
for @{ 'one }.
interpretation "Rone" 'one = (R1).
interpretation "None" 'one = (S O).

interpretation "Rplus" 'plus x y = (Rplus x y).

interpretation "Rmult" 'middot x y = (Rmult x y).

definition Fplus ≝
 λf,g:R→R.λx:R.f x + g x.
 
definition Fmult ≝
 λf,g:R→R.λx:R.f x · g x.

interpretation "Fplus" 'plus x y = (Fplus x y).
interpretation "Fmult" 'middot x y = (Fmult x y).

notation "2" with precedence 89
for @{ 'two }.
interpretation "Rtwo" 'two = (Rplus R1 R1).
interpretation "Ntwo" 'two = (S (S O)).

let rec Rpower (x:R) (n:nat) on n ≝
 match n with
  [ O ⇒ 1
  | S n ⇒ x · (Rpower x n)
  ].

interpretation "Rpower" 'exp x n = (Rpower x n).

let rec inj (n:nat) on n : R ≝
 match n with
  [ O ⇒ 0
  | S n ⇒
     match n with
      [ O ⇒ 1
      | S m ⇒ 1 + inj n
      ]
  ].

coercion inj.

axiom Rplus_Rzero_x: ∀x:R.0+x=x.
axiom Rplus_comm: symmetric ? Rplus.
axiom Rplus_assoc: associative ? Rplus.
axiom Rmult_Rone_x: ∀x:R.1 · x=x.
axiom Rmult_Rzero_x: ∀x:R.0 · x=0.
axiom Rmult_assoc: associative ? Rmult.
axiom Rmult_comm: symmetric ? Rmult.
axiom Rmult_Rplus_distr: distributive ? Rmult Rplus.

alias symbol "middot" = "Rmult".
alias symbol "plus" = "natural plus".

definition monomio ≝
 λn.λx:R.x\sup n.

definition costante : nat → R → R ≝
 λa:nat.λx:R.inj a.

coercion costante with 1.

axiom f_eq_extensional:
 ∀f,g:R→R.(∀x:R.f x = g x) → f=g.

lemma Fmult_one_f: ∀f:R→R.1·f=f.
 intro;
 unfold Fmult;
 simplify;
 apply f_eq_extensional;
 intro;
 autobatch.
qed.

lemma Fmult_zero_f: ∀f:R→R.0·f=0.
 intro;
 unfold Fmult;
 simplify;
 apply f_eq_extensional;
 intro;
 autobatch.
qed.

lemma Fmult_commutative: symmetric ? Fmult.
 unfold;
 intros;
 unfold Fmult;
 apply f_eq_extensional;
 intros;
 autobatch.
qed.

lemma Fmult_associative: associative ? Fmult.
 unfold;
 intros;
 unfold Fmult;
 unfold Fmult;
 apply f_eq_extensional;
 intros;
 autobatch.
qed.

lemma Fmult_Fplus_distr: distributive ? Fmult Fplus.
 unfold;
 intros;
 unfold Fmult;
 unfold Fplus;
 apply f_eq_extensional;
 intros;
 simplify;
 autobatch.
qed.

lemma monomio_product:
 ∀n,m.monomio (n+m) = monomio n · monomio m.
 intros;
 unfold monomio;
 unfold Fmult;
 simplify;
 elim n;
  [ simplify;
    apply f_eq_extensional;
    intro;
    autobatch
  | simplify;
    apply f_eq_extensional;
    intro;
    cut (x\sup (n1+m) = x \sup n1 · x \sup m);
     [ rewrite > Hcut;
       autobatch
     | change in ⊢ (? ? % ?) with ((λx:R.x\sup(n1+m)) x);
       rewrite > H;
       reflexivity
     ]
  ].
qed.

lemma costante_sum:
 ∀n,m.costante n + costante m = costante (n+m).
 intros;
 unfold Fplus;
 unfold costante;
 apply f_eq_extensional;
 intros;
 elim n;
  [ simplify;
    autobatch
  | simplify;
    clear x;
    clear H;
    clear n;
    elim n1;
     [ simplify;
       elim m;
        [ simplify;
          autobatch
        | simplify;
          rewrite < H;
          autobatch
        ]
     | simplify;
       rewrite < H;
       clear H;
       elim n;
        [ simplify;
          autobatch
        | simplify;
          autobatch
        ]
     ]
   ].
qed.

axiom derivative: (R→R) → R → R.

notation "hvbox('D'[f])"
  non associative with precedence 90
for @{ 'derivative $f }.

interpretation "Rderivative" 'derivative f = (derivative f).

(*  FG: we definitely do not want 'x' as a keyward! 
 *  Any file that includes this one can not use 'x' as an identifier
 *)  
notation "hvbox('X' \sup n)"
  non associative with precedence 65
for @{ 'monomio $n }.

notation "hvbox('X')"
  non associative with precedence 65
for @{ 'monomio 1 }.

interpretation "Rmonomio" 'monomio n = (monomio n).

axiom derivative_x0: D[X \sup 0] = 0.
axiom derivative_x1: D[X] = 1.

axiom derivative_mult: ∀f,g:R→R. D[f·g] = D[f]·g + f·D[g].

alias symbol "middot" = "Fmult".

theorem derivative_power: ∀n:nat. D[X \sup n] = n·X \sup (pred n).
 assume n:nat.
 (*we proceed by induction on n to prove
 (D[X \sup n] = n · X \sup (pred n)).*)
 elim n 0.
 case O.
   the thesis becomes (D[X \sup 0] = 0·X \sup (pred 0)).
  done.
 case S (m:nat).
  by induction hypothesis we know
   (D[X \sup m] = m·X \sup (pred m)) (H).
  the thesis becomes
   (D[X \sup (1+m)] = (1+m) · X \sup m).
  we need to prove
   (m · (X \sup (1+ pred m)) = m · X \sup m) (Ppred).
   lapply depth=0 le_n;
   we proved (0 < m ∨ 0=m) (cases).
   we proceed by induction on cases
   to prove (m · (X \sup (1+ pred m)) = m · X \sup m).
    case left.
      suppose (0 < m) (m_pos).
      using (S_pred ? m_pos) we proved (m = 1 + pred m) (H1).
      by H1 done.
    case right.
      suppose (0=m) (m_zero). 
    by m_zero, Fmult_zero_f done.
  conclude
     (D[X \sup (1+m)])
   = (D[X · X \sup m]).
   = (D[X] · X \sup m + X · D[X \sup m]).
   = (X \sup m + X · (m · X \sup (pred m))). 
   lapply depth=0 Fmult_associative;
   lapply depth=0 Fmult_commutative;
   = (X \sup m + m · (X · X \sup (pred m))) by Fmult_associative, Fmult_commutative.
   = (X \sup m + m · (X \sup (1 + pred m))).
   = (X \sup m + m · X \sup m).
   = ((1+m) · X \sup m) by Fmult_one_f, Fmult_commutative, Fmult_Fplus_distr, costante_sum
  done.
qed.

(*
notation "hvbox(\frac 'd' ('d' ident i) break p)"
  right associative with precedence 90
for @{ 'derivative ${default
  @{\lambda ${ident i} : $ty. $p)}
  @{\lambda ${ident i} . $p}}}.

interpretation "Rderivative" 'derivative \eta.f = (derivative f).
*)

notation "hvbox(\frac 'd' ('d' 'X') break p)" with precedence 90
for @{ 'derivative $p}.

interpretation "Rderivative" 'derivative f = (derivative f).

theorem derivative_power': ∀n:nat. D[X \sup (1+n)] = (1+n) · X \sup n.
 assume n:nat.
 (*we proceed by induction on n to prove
 (D[X \sup (1+n)] = (1+n) · X \sup n).*) elim n 0.
 case O.
   the thesis becomes (D[X \sup 1] = 1 · X \sup 0).
  done.
 case S (m:nat).
  by induction hypothesis we know
   (D[X \sup (1+m)] = (1+m) · X \sup m) (H).
  the thesis becomes
   (D[X \sup (2+m)] = (2+m) · X \sup (1+m)).
  conclude
     (D[X \sup (2+m)])
   = (D[X · X \sup (1+m)]).
   = (D[X] · X \sup (1+m) + X · D[X \sup (1+m)]).
   = (X \sup (1+m) + X · (costante (1+m) · X \sup m)).
   = (X \sup (1+m) + costante (1+m) · X \sup (1+m)).
   = ((2+m) · X \sup (1+m)) timeout=30 by Fmult_one_f, Fmult_commutative,
       Fmult_Fplus_distr, assoc_plus, plus_n_SO, costante_sum
  done.
qed.

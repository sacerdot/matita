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

set "baseuri" "cic:/matita/demo/power_derivative".

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
interpretation "Rzero" 'zero =
 (cic:/matita/demo/power_derivative/R0.con).
interpretation "Nzero" 'zero =
 (cic:/matita/nat/nat/nat.ind#xpointer(1/1/1)).

notation "1" with precedence 89
for @{ 'one }.
interpretation "Rone" 'one =
 (cic:/matita/demo/power_derivative/R1.con).
interpretation "None" 'one =
 (cic:/matita/nat/nat/nat.ind#xpointer(1/1/2)
   cic:/matita/nat/nat/nat.ind#xpointer(1/1/1)).

interpretation "Rplus" 'plus x y =
 (cic:/matita/demo/power_derivative/Rplus.con x y).

notation "hvbox(a break \middot b)" 
  left associative with precedence 55
for @{ 'times $a $b }.

interpretation "Rmult" 'times x y =
 (cic:/matita/demo/power_derivative/Rmult.con x y).

definition Fplus ≝
 λf,g:R→R.λx:R.f x + g x.
 
definition Fmult ≝
 λf,g:R→R.λx:R.f x · g x.

interpretation "Fplus" 'plus x y =
 (cic:/matita/demo/power_derivative/Fplus.con x y).
interpretation "Fmult" 'times x y =
 (cic:/matita/demo/power_derivative/Fmult.con x y).

notation "2" with precedence 89
for @{ 'two }.
interpretation "Rtwo" 'two =
 (cic:/matita/demo/power_derivative/Rplus.con
   cic:/matita/demo/power_derivative/R1.con
   cic:/matita/demo/power_derivative/R1.con).
interpretation "Ntwo" 'two =
 (cic:/matita/nat/nat/nat.ind#xpointer(1/1/2)
   (cic:/matita/nat/nat/nat.ind#xpointer(1/1/2)
     (cic:/matita/nat/nat/nat.ind#xpointer(1/1/1)))).

let rec Rpower (x:R) (n:nat) on n ≝
 match n with
  [ O ⇒ 1
  | S n ⇒ x · (Rpower x n)
  ].

interpretation "Rpower" 'exp x n =
 (cic:/matita/demo/power_derivative/Rpower.con x n).

let rec inj (n:nat) on n : R ≝
 match n with
  [ O ⇒ 0
  | S n ⇒
     match n with
      [ O ⇒ 1
      | S m ⇒ 1 + inj n
      ]
  ].

coercion cic:/matita/demo/power_derivative/inj.con.

axiom Rplus_Rzero_x: ∀x:R.0+x=x.
axiom Rplus_comm: symmetric ? Rplus.
axiom Rplus_assoc: associative ? Rplus.
axiom Rmult_Rone_x: ∀x:R.1*x=x.
axiom Rmult_Rzero_x: ∀x:R.0*x=0.
axiom Rmult_assoc: associative ? Rmult.
axiom Rmult_comm: symmetric ? Rmult.
axiom Rmult_Rplus_distr: distributive ? Rmult Rplus.

alias symbol "times" = "Rmult".
alias symbol "plus" = "natural plus".

definition monomio ≝
 λn.λx:R.x\sup n.

definition costante : nat → R → R ≝
 λa:nat.λx:R.inj a.

coercion cic:/matita/demo/power_derivative/costante.con 1.

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

interpretation "Rderivative" 'derivative f =
 (cic:/matita/demo/power_derivative/derivative.con f).

notation "hvbox('x' \sup n)"
  non associative with precedence 60
for @{ 'monomio $n }.

notation "hvbox('x')"
  non associative with precedence 60
for @{ 'monomio 1 }.

interpretation "Rmonomio" 'monomio n =
 (cic:/matita/demo/power_derivative/monomio.con n).

axiom derivative_x0: D[x \sup 0] = 0.
axiom derivative_x1: D[x] = 1.
axiom derivative_mult: ∀f,g:R→R. D[f·g] = D[f]·g + f·D[g].

alias symbol "times" = "Fmult".

theorem derivative_power: ∀n:nat. D[x \sup n] = n·x \sup (pred n).
 assume n:nat.
 (*we proceed by induction on n to prove
 (D[x \sup n] = n · x \sup (pred n)).*)
 elim n 0.
 case O.
   the thesis becomes (D[x \sup 0] = 0·x \sup (pred 0)).
   by _
  done.
 case S (m:nat).
  by induction hypothesis we know
   (D[x \sup m] = m·x \sup (pred m)) (H).
  the thesis becomes
   (D[x \sup (1+m)] = (1+m) · x \sup m).
  we need to prove
   (m · (x \sup (1+ pred m)) = m · x \sup m) (Ppred).
   by _ we proved (0 < m ∨ 0=m) (cases).
   we proceed by induction on cases
   to prove (m · (x \sup (1+ pred m)) = m · x \sup m).
    case left.
      suppose (0 < m) (m_pos).
      by (S_pred m m_pos) we proved (m = 1 + pred m) (H1).
      by _
     done.
    case right.
      suppose (0=m) (m_zero). by _ done.
  conclude
     (D[x \sup (1+m)])
   = (D[x · x \sup m]) by _.
   = (D[x] · x \sup m + x · D[x \sup m]) by _.
   = (x \sup m + x · (m · x \sup (pred m))) by _.
clear H.
   = (x \sup m + m · (x \sup (1 + pred m))) by _.
   = (x \sup m + m · x \sup m) by _.
   = ((1+m) · x \sup m) by _ (timeout=30)
  done.
qed.

(*
notation "hvbox(\frac 'd' ('d' ident i) break p)"
  right associative with precedence 90
for @{ 'derivative ${default
  @{\lambda ${ident i} : $ty. $p)}
  @{\lambda ${ident i} . $p}}}.

interpretation "Rderivative" 'derivative \eta.f =
 (cic:/matita/demo/power_derivative/derivative.con f).
*)

notation "hvbox(\frac 'd' ('d' 'x') break p)"
  right associative with precedence 90
for @{ 'derivative $p}.

interpretation "Rderivative" 'derivative f =
 (cic:/matita/demo/power_derivative/derivative.con f).

theorem derivative_power': ∀n:nat. D[x \sup (1+n)] = (1+n) · x \sup n.
 assume n:nat.
 (*we proceed by induction on n to prove
 (D[x \sup (1+n)] = (1+n) · x \sup n).*) elim n 0.
 case O.
   the thesis becomes (D[x \sup 1] = 1 · x \sup 0).
   by _
  done.
 case S (m:nat).
  by induction hypothesis we know
   (D[x \sup (1+m)] = (1+m) · x \sup m) (H).
  the thesis becomes
   (D[x \sup (2+m)] = (2+m) · x \sup (1+m)).
  conclude
     (D[x \sup (2+m)])
   = (D[x · x \sup (1+m)]) by _.
   = (D[x] · x \sup (1+m) + x · D[x \sup (1+m)]) by _.
   = (x \sup (1+m) + x · (costante (1+m) · x \sup m)) by _.
clear H.
   = (x \sup (1+m) + costante (1+m) · x \sup (1+m)) by _.
   = (x \sup (1+m) · (costante (2 + m))) by _
  done.
qed.
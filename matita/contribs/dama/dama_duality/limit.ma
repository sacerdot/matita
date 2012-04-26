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

include "infsup.ma".

definition shift ≝ λT:Type.λs:sequence T.λk:nat.λn.s (n+k).

(* 3.28 *)
definition limsup ≝
  λE:excess.λxn:sequence E.λx:E.∃alpha:sequence E. 
    (∀k.(alpha k) is_strong_sup (shift ? xn k) in E) ∧ 
     x is_strong_inf alpha in E.     

notation < "x \nbsp 'is_limsup' \nbsp s" non associative with precedence 55 for @{'limsup $_ $s $x}.
notation < "x \nbsp 'is_liminf' \nbsp s" non associative with precedence 55 for @{'liminf $_ $s $x}.
notation > "x 'is_limsup' s 'in' e" non associative with precedence 55 for @{'limsup $e $s $x}.
notation > "x 'is_liminf' s 'in' e" non associative with precedence 55 for @{'liminf $e $s $x}.

interpretation "Excess limsup" 'limsup e s x = (limsup e s x).
interpretation "Excess liminf" 'liminf e s x = (limsup (dual_exc e) s x).

(* 3.29 *)  
definition lim ≝ 
  λE:excess.λxn:sequence E.λx:E. x is_limsup xn in E ∧ x is_liminf xn in E.

notation < "x \nbsp 'is_lim' \nbsp s" non associative with precedence 55 for @{'lim $_ $s $x}.
notation > "x 'is_lim' s 'in' e" non associative with precedence 55 for @{'lim $e $s $x}.
interpretation "Excess lim" 'lim e s x = (lim e s x).

lemma sup_decreasing:
  ∀E:excess.∀xn:sequence E.
   ∀alpha:sequence E. (∀k.(alpha k) is_strong_sup xn in E) → 
     alpha is_decreasing in E.
intros (E xn alpha H); unfold strong_sup in H; unfold upper_bound in H; unfold;
intro r; 
elim (H r) (H1r H2r);
elim (H (S r)) (H1sr H2sr); clear H H2r H1sr;
intro e; cases (H2sr (alpha r) e) (w Hw); clear e H2sr;
cases (H1r w Hw);
qed.

include "tend.ma".
include "metric_lattice.ma".
  
(* 3.30 *)   
lemma lim_tends: 
  ∀R.∀ml:mlattice R.∀xn:sequence ml.∀x:ml.
    x is_lim xn in ml → xn ⇝ x.
intros (R ml xn x Hl); unfold lim in Hl; unfold limsup in Hl;
cases Hl (e1 e2); cases e1 (an Han); cases e2 (bn Hbn); clear Hl e1 e2;
cases Han (SSan SIxan); cases Hbn (SSbn SIxbn); clear Han Hbn;
cases SIxan (LBxan Hxg); cases SIxbn (UPxbn Hxl); clear SIxbn SIxan;
change in UPxbn:(%) with (x is_lower_bound bn in ml);
unfold upper_bound in UPxbn LBxan; change  
intros (e He);  
(* 2.6 OC *)

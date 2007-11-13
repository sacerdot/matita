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

set "baseuri" "cic:/matita/groups/".

include "excedence.ma".

definition left_neutral ≝ λC:apartness.λop.λe:C. ∀x:C. op e x ≈ x.
definition right_neutral ≝ λC:apartness.λop. λe:C. ∀x:C. op x e ≈ x.
definition left_inverse ≝ λC:apartness.λop.λe:C.λinv:C→C. ∀x:C. op (inv x) x ≈ e.
definition right_inverse ≝ λC:apartness.λop.λe:C.λ inv: C→ C. ∀x:C. op x (inv x) ≈ e. 
definition strong_ext ≝ λA:apartness.λop:A→A.∀x,y. op x # op y → x # y.
(* ALLOW DEFINITION WITH SOME METAS *)

definition distributive_left ≝
 λA:apartness.λf:A→A→A.λg:A→A→A.
  ∀x,y,z. f x (g y z) ≈ g (f x y) (f x z).

definition distributive_right ≝
 λA:apartness.λf:A→A→A.λg:A→A→A.
  ∀x,y,z. f (g x y) z ≈ g (f x z) (f y z).

record abelian_group : Type ≝
 { carr:> apartness;
   plus: carr → carr → carr;
   zero: carr;
   opp: carr → carr;
   plus_assoc: associative ? plus (eq carr);
   plus_comm: commutative ? plus (eq carr);
   zero_neutral: left_neutral ? plus zero;
   opp_inverse: left_inverse ? plus zero opp;
   plus_strong_ext: ∀z.strong_ext ? (plus z)  
}.
 
notation "0" with precedence 89 for @{ 'zero }.

interpretation "Abelian group zero" 'zero =
 (cic:/matita/groups/zero.con _).

interpretation "Abelian group plus" 'plus a b =
 (cic:/matita/groups/plus.con _ a b).

interpretation "Abelian group opp" 'uminus a =
 (cic:/matita/groups/opp.con _ a).

definition minus ≝
 λG:abelian_group.λa,b:G. a + -b.

interpretation "Abelian group minus" 'minus a b =
 (cic:/matita/groups/minus.con _ a b).
 
lemma ap_rewl: ∀A:apartness.∀x,z,y:A. x ≈ y → y # z → x # z.
intros (A x z y Exy Ayz); cases (ap_cotransitive ???x Ayz); [2:assumption]
cases (Exy (ap_symmetric ??? a));
qed.
  
lemma ap_rewr: ∀A:apartness.∀x,z,y:A. x ≈ y → z # y → z # x.
intros (A x z y Exy Azy); apply ap_symmetric; apply (ap_rewl ???? Exy);
apply ap_symmetric; assumption;
qed.

definition ext ≝ λA:apartness.λop:A→A. ∀x,y. x ≈ y → op x ≈ op y.

lemma strong_ext_to_ext: ∀A:apartness.∀op:A→A. strong_ext ? op → ext ? op.
intros 6 (A op SEop x y Exy); intro Axy; apply Exy; apply SEop; assumption;
qed. 

lemma f_plusl: ∀G:abelian_group.∀x,y,z:G. y ≈ z →  x+y ≈ x+z.
intros (G x y z Eyz); apply (strong_ext_to_ext ?? (plus_strong_ext ? x));
assumption;
qed.  
   
lemma plus_strong_extr: ∀G:abelian_group.∀z:G.strong_ext ? (λx.x + z).
intros 5 (G z x y A); simplify in A;
lapply (plus_comm ? z x) as E1; lapply (plus_comm ? z y) as E2;
lapply (ap_rewl ???? E1 A) as A1; lapply (ap_rewr ???? E2 A1) as A2;
apply (plus_strong_ext ???? A2);
qed.
   
lemma feq_plusr: ∀G:abelian_group.∀x,y,z:G. y ≈ z →  y+x ≈ z+x.
intros (G x y z Eyz); apply (strong_ext_to_ext ?? (plus_strong_extr ? x));
assumption;
qed.   
   
lemma fap_plusl: ∀G:abelian_group.∀x,y,z:G. y # z →  x+y # x+z. 
intros (G x y z Ayz); apply (plus_strong_ext ? (-x));
apply (ap_rewl ??? ((-x + x) + y));
[1: apply plus_assoc; 
|2: apply (ap_rewr ??? ((-x +x) +z));
    [1: apply plus_assoc; 
    |2: apply (ap_rewl ??? (0 + y));
        [1: apply (feq_plusr ???? (opp_inverse ??)); 
        |2: apply (ap_rewl ???? (zero_neutral ? y)); apply (ap_rewr ??? (0 + z));
            [1: apply (feq_plusr ???? (opp_inverse ??)); 
            |2: apply (ap_rewr ???? (zero_neutral ? z)); assumption;]]]]
qed.

lemma plus_canc: ∀G:abelian_group.∀x,y,z:G. x+y ≈ x+z → y ≈ z. 
intros 6 (G x y z E Ayz); apply E; apply fap_plusl; assumption;
qed. 

(*

theorem eq_opp_plus_plus_opp_opp: ∀G:abelian_group.∀x,y:G. -(x+y) = -x + -y.
 intros;
 apply (cancellationlaw ? (x+y));
 rewrite < plus_comm;
 rewrite > opp_inverse;
 rewrite > plus_assoc;
 rewrite > plus_comm in ⊢ (? ? ? (? ? ? (? ? ? %)));
 rewrite < plus_assoc in ⊢ (? ? ? (? ? ? %));
 rewrite > plus_comm;
 rewrite > plus_comm in ⊢ (? ? ? (? ? (? ? % ?) ?));
 rewrite > opp_inverse;
 rewrite > zero_neutral;
 rewrite > opp_inverse;
 reflexivity.
qed.

theorem eq_opp_opp_x_x: ∀G:abelian_group.∀x:G.--x=x.
 intros;
 apply (cancellationlaw ? (-x));
 rewrite > opp_inverse;
 rewrite > plus_comm;
 rewrite > opp_inverse;
 reflexivity.
qed.

theorem eq_zero_opp_zero: ∀G:abelian_group.0=-0.
 [ assumption
 | intros;
   apply (cancellationlaw ? 0);
   rewrite < plus_comm in ⊢ (? ? ? %);
   rewrite > opp_inverse;
   rewrite > zero_neutral;
   reflexivity
 ].
qed.

*)
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

include "higher_order_defs/functions.ma".
include "nat/nat.ma".
include "nat/orders.ma".
include "constructive_connectives.ma".

definition left_neutral \def λC,op.λe:C. ∀x:C. op e x = x.

definition right_neutral \def λC,op. λe:C. ∀x:C. op x e=x.

definition left_inverse \def λC,op.λe:C.λinv:C→C. ∀x:C. op (inv x) x = e.

definition right_inverse \def λC,op.λe:C.λ inv: C→ C. ∀x:C. op x (inv x)=e. 

definition distributive_left ≝
 λA:Type.λf:A→A→A.λg:A→A→A.
  ∀x,y,z. f x (g y z) = g (f x y) (f x z).

definition distributive_right ≝
 λA:Type.λf:A→A→A.λg:A→A→A.
  ∀x,y,z. f (g x y) z = g (f x z) (f y z).

record is_abelian_group (C:Type) (plus:C→C→C) (zero:C) (opp:C→C) : Prop \def
 { (* abelian additive semigroup properties *)
    plus_assoc_: associative ? plus;
    plus_comm_: symmetric ? plus;
    (* additive monoid properties *)
    zero_neutral_: left_neutral ? plus zero;
    (* additive group properties *)
    opp_inverse_: left_inverse ? plus zero opp
 }.

record abelian_group : Type \def
 { carrier:> Type;
   plus: carrier → carrier → carrier;
   zero: carrier;
   opp: carrier → carrier;
   ag_abelian_group_properties: is_abelian_group ? plus zero opp
 }.
 
notation "0" with precedence 89
for @{ 'zero }.

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
 
theorem plus_assoc: ∀G:abelian_group. associative ? (plus G).
 intro;
 apply (plus_assoc_ ? ? ? ? (ag_abelian_group_properties G)).
qed.

theorem plus_comm: ∀G:abelian_group. symmetric ? (plus G).
 intro;
 apply (plus_comm_ ? ? ? ? (ag_abelian_group_properties G)).
qed.

theorem zero_neutral: ∀G:abelian_group. left_neutral ? (plus G) 0.
 intro;
 apply (zero_neutral_ ? ? ? ? (ag_abelian_group_properties G)).
qed.

theorem opp_inverse: ∀G:abelian_group. left_inverse ? (plus G) 0 (opp G).
 intro;
 apply (opp_inverse_ ? ? ? ? (ag_abelian_group_properties G)).
qed.

lemma cancellationlaw: ∀G:abelian_group.∀x,y,z:G. x+y=x+z → y=z. 
intros;
generalize in match (eq_f ? ? (λa.-x +a) ? ? H);
intros; clear H;
rewrite < plus_assoc in H1;
rewrite < plus_assoc in H1;
rewrite > opp_inverse in H1;
rewrite > zero_neutral in H1;
rewrite > zero_neutral in H1;
assumption.
qed.

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
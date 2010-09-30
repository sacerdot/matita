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



include "excess.ma".

definition left_neutral ≝ λC:apartness.λop.λe:C. ∀x:C. op e x ≈ x.
definition right_neutral ≝ λC:apartness.λop. λe:C. ∀x:C. op x e ≈ x.
definition left_inverse ≝ λC:apartness.λop.λe:C.λinv:C→C. ∀x:C. op (inv x) x ≈ e.
definition right_inverse ≝ λC:apartness.λop.λe:C.λ inv: C→ C. ∀x:C. op x (inv x) ≈ e. 
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
   plus_assoc_: associative ? plus (eq carr);
   plus_comm_: commutative ? plus (eq carr);
   zero_neutral_: left_neutral ? plus zero;
   opp_inverse_: left_inverse ? plus zero opp;
   plus_strong_ext: ∀z.strong_ext ? (plus z)  
}.

notation "0" with precedence 89 for @{ 'zero }.

interpretation "Abelian group zero" 'zero = (zero ?).

interpretation "Abelian group plus" 'plus a b = (plus ? a b).

interpretation "Abelian group opp" 'uminus a = (opp ? a).

definition minus ≝
 λG:abelian_group.λa,b:G. a + -b.

interpretation "Abelian group minus" 'minus a b = (minus ? a b).

lemma plus_assoc: ∀G:abelian_group.∀x,y,z:G.x+(y+z)≈x+y+z ≝ plus_assoc_. 
lemma plus_comm: ∀G:abelian_group.∀x,y:G.x+y≈y+x ≝ plus_comm_. 
lemma zero_neutral: ∀G:abelian_group.∀x:G.0+x≈x ≝ zero_neutral_. 
lemma opp_inverse: ∀G:abelian_group.∀x:G.-x+x≈0 ≝ opp_inverse_.

definition ext ≝ λA:apartness.λop:A→A. ∀x,y. x ≈ y → op x ≈ op y.

lemma strong_ext_to_ext: ∀A:apartness.∀op:A→A. strong_ext ? op → ext ? op.
intros 6 (A op SEop x y Exy); intro Axy; apply Exy; apply SEop; assumption;
qed. 

lemma feq_plusl: ∀G:abelian_group.∀x,y,z:G. y ≈ z →  x+y ≈ x+z.
intros (G x y z Eyz); apply (strong_ext_to_ext ?? (plus_strong_ext ? x));
assumption;
qed.  

coercion cic:/matita/group/feq_plusl.con nocomposites.
   
lemma plus_strong_extr: ∀G:abelian_group.∀z:G.strong_ext ? (λx.x + z).
intros 5 (G z x y A); simplify in A;
lapply (plus_comm ? z x) as E1; lapply (plus_comm ? z y) as E2;
lapply (Ap≪ ? E1 A) as A1; lapply (Ap≫ ? E2 A1) as A2;
apply (plus_strong_ext ???? A2);
qed.

lemma plus_cancl_ap: ∀G:abelian_group.∀x,y,z:G.z+x # z + y → x # y.
intros; apply plus_strong_ext; assumption;
qed.

lemma plus_cancr_ap: ∀G:abelian_group.∀x,y,z:G.x+z # y+z → x # y.
intros; apply plus_strong_extr; assumption;
qed.
   
lemma feq_plusr: ∀G:abelian_group.∀x,y,z:G. y ≈ z →  y+x ≈ z+x.
intros (G x y z Eyz); apply (strong_ext_to_ext ?? (plus_strong_extr ? x));
assumption;
qed.   
   
coercion cic:/matita/group/feq_plusr.con nocomposites.

(* generation of coercions to make *_rew[lr] easier *)
lemma feq_plusr_sym_: ∀G:abelian_group.∀x,y,z:G.z ≈ y →  y+x ≈ z+x.
compose feq_plusr with eq_sym (H); apply H; assumption;
qed.
coercion cic:/matita/group/feq_plusr_sym_.con nocomposites.
lemma feq_plusl_sym_: ∀G:abelian_group.∀x,y,z:G.z ≈ y →  x+y ≈ x+z.
compose feq_plusl with eq_sym (H); apply H; assumption;
qed.
coercion cic:/matita/group/feq_plusl_sym_.con nocomposites.
      
lemma fap_plusl: ∀G:abelian_group.∀x,y,z:G. y # z →  x+y # x+z. 
intros (G x y z Ayz); apply (plus_strong_ext ? (-x));
apply (Ap≪ ((-x + x) + y));
[1: apply plus_assoc; 
|2: apply (Ap≫ ((-x +x) +z));
    [1: apply plus_assoc; 
    |2: apply (Ap≪ (0 + y));
        [1: apply (feq_plusr ???? (opp_inverse ??)); 
        |2: apply (Ap≪ ? (zero_neutral ? y)); 
            apply (Ap≫ (0 + z) (opp_inverse ??)); 
            apply (Ap≫ ? (zero_neutral ??)); assumption;]]]
qed.

lemma fap_plusr: ∀G:abelian_group.∀x,y,z:G. y # z →  y+x # z+x. 
intros (G x y z Ayz); apply (plus_strong_extr ? (-x));
apply (Ap≪ (y + (x + -x)));
[1: apply (eq_sym ??? (plus_assoc ????)); 
|2: apply (Ap≫ (z + (x + -x)));
    [1: apply (eq_sym ??? (plus_assoc ????)); 
    |2: apply (Ap≪ (y + (-x+x)) (plus_comm ? x (-x)));
        apply (Ap≪ (y + 0) (opp_inverse ??));
        apply (Ap≪ (0 + y) (plus_comm ???));
        apply (Ap≪ y (zero_neutral ??));
        apply (Ap≫ (z + (-x+x)) (plus_comm ? x (-x)));
        apply (Ap≫ (z + 0) (opp_inverse ??));
        apply (Ap≫ (0 + z) (plus_comm ???));
        apply (Ap≫ z (zero_neutral ??));
        assumption]]
qed.

lemma applus: ∀E:abelian_group.∀x,a,y,b:E.x + a # y + b → x # y ∨ a # b.
intros; cases (ap_cotransitive ??? (y+a) a1); [left|right]
[apply (plus_cancr_ap ??? a)|apply (plus_cancl_ap ??? y)]
assumption;
qed.
    
lemma plus_cancl: ∀G:abelian_group.∀y,z,x:G. x+y ≈ x+z → y ≈ z. 
intros 6 (G y z x E Ayz); apply E; apply fap_plusl; assumption;
qed.

lemma plus_cancr: ∀G:abelian_group.∀y,z,x:G. y+x ≈ z+x → y ≈ z. 
intros 6 (G y z x E Ayz); apply E; apply fap_plusr; assumption;
qed.

theorem eq_opp_plus_plus_opp_opp: 
  ∀G:abelian_group.∀x,y:G. -(x+y) ≈ -x + -y.
intros (G x y); apply (plus_cancr ??? (x+y));
apply (Eq≈ 0 (opp_inverse ??));
apply (Eq≈ (-x + -y + x + y)); [2: apply (eq_sym ??? (plus_assoc ????))]
apply (Eq≈ (-y + -x + x + y)); [2: repeat apply feq_plusr; apply plus_comm]
apply (Eq≈ (-y + (-x + x) + y)); [2: apply feq_plusr; apply plus_assoc;]
apply (Eq≈ (-y + 0 + y)); 
  [2: apply feq_plusr; apply feq_plusl; apply eq_sym; apply opp_inverse]
apply (Eq≈ (-y + y)); 
  [2: apply feq_plusr; apply eq_sym; 
      apply (Eq≈ (0+-y)); [apply plus_comm|apply zero_neutral]]
apply eq_sym; apply opp_inverse.
qed.

theorem eq_opp_opp_x_x: ∀G:abelian_group.∀x:G.--x ≈ x.
intros (G x); apply (plus_cancl ??? (-x));
apply (Eq≈ (--x + -x) (plus_comm ???));
apply (Eq≈ 0 (opp_inverse ??));
apply eq_sym; apply opp_inverse;
qed.

theorem eq_zero_opp_zero: ∀G:abelian_group.0 ≈ -0. [assumption]
intro G; apply (plus_cancr ??? 0);
apply (Eq≈ 0); [apply zero_neutral;]
apply eq_sym; apply opp_inverse;
qed.

lemma feq_oppr: ∀G:abelian_group.∀x,y,z:G. y ≈ z → x ≈ -y → x ≈ -z.
intros (G x y z H1 H2); apply (plus_cancr ??? z);
apply (Eq≈ 0 ? (opp_inverse ??));
apply (Eq≈ (-y + z) H2);
apply (Eq≈ (-y + y) H1);
apply (Eq≈ 0 (opp_inverse ??));
apply eq_reflexive;
qed.

lemma feq_oppl: ∀G:abelian_group.∀x,y,z:G. y ≈ z → -y ≈ x → -z ≈ x.
intros (G x y z H1 H2); apply eq_sym; apply (feq_oppr ??y);
[2:apply eq_sym] assumption;
qed.

lemma feq_opp: ∀G:abelian_group.∀x,y:G. x ≈ y → -x ≈ -y.
intros (G x y H); apply (feq_oppl ??y ? H); apply eq_reflexive;
qed.

coercion cic:/matita/group/feq_opp.con nocomposites.

lemma eq_opp_sym: ∀G:abelian_group.∀x,y:G. y ≈ x → -x ≈ -y.
compose feq_opp with eq_sym (H); apply H; assumption;
qed.

coercion cic:/matita/group/eq_opp_sym.con nocomposites.

lemma eq_opp_plusr: ∀G:abelian_group.∀x,y,z:G. x ≈ y → -(x + z) ≈ -(y + z).
compose feq_plusr with feq_opp(H); apply H; assumption;
qed.

coercion cic:/matita/group/eq_opp_plusr.con nocomposites.

lemma eq_opp_plusl: ∀G:abelian_group.∀x,y,z:G. x ≈ y → -(z + x) ≈ -(z + y).
compose feq_plusl with feq_opp(H); apply H; assumption;
qed.

coercion cic:/matita/group/eq_opp_plusl.con nocomposites.

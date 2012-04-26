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

include "logic/cprop_connectives.ma".

definition Type0 := Type.
definition Type1 := Type.
definition Type2 := Type.
definition Type0_lt_Type1 := (Type0 : Type1).
definition Type1_lt_Type2 := (Type1 : Type2).

record equivalence_relation (A:Type) : Type ≝
 { eq_rel:2> A → A → CProp;
   refl: reflexive ? eq_rel;
   sym: symmetric ? eq_rel;
   trans: transitive ? eq_rel
 }.

record setoid : Type1 ≝
 { carr:> Type;
   eq: equivalence_relation carr
 }.

definition reflexive1 ≝ λA:Type.λR:A→A→CProp.∀x:A.R x x.
definition symmetric1 ≝ λC:Type.λlt:C→C→CProp. ∀x,y:C.lt x y → lt y x.
definition transitive1 ≝ λA:Type.λR:A→A→CProp.∀x,y,z:A.R x y → R y z → R x z.

record equivalence_relation1 (A:Type) : Type2 ≝
 { eq_rel1:2> A → A → CProp;
   refl1: reflexive1 ? eq_rel1;
   sym1: symmetric1 ? eq_rel1;
   trans1: transitive1 ? eq_rel1
 }.

record setoid1: Type ≝
 { carr1:> Type;
   eq1: equivalence_relation1 carr1
 }.

definition setoid1_of_setoid: setoid → setoid1.
 intro;
 constructor 1;
  [ apply (carr s)
  | constructor 1;
    [ apply (eq_rel s);
      apply (eq s)
    | apply (refl s)
    | apply (sym s)
    | apply (trans s)]]
qed.

coercion setoid1_of_setoid.

(*
definition Leibniz: Type → setoid.
 intro;
 constructor 1;
  [ apply T
  | constructor 1;
     [ apply (λx,y:T.cic:/matita/logic/equality/eq.ind#xpointer(1/1) ? x y)
     | alias id "refl_eq" = "cic:/matita/logic/equality/eq.ind#xpointer(1/1/1)".
       apply refl_eq
     | alias id "sym_eq" = "cic:/matita/logic/equality/sym_eq.con".
       apply sym_eq
     | alias id "trans_eq" = "cic:/matita/logic/equality/trans_eq.con".
       apply trans_eq ]]
qed.

coercion Leibniz.
*)

interpretation "setoid1 eq" 'eq t x y = (eq_rel1 ? (eq1 t) x y).
interpretation "setoid eq" 'eq t x y = (eq_rel ? (eq t) x y).
interpretation "setoid1 symmetry" 'invert r = (sym1 ???? r).
interpretation "setoid symmetry" 'invert r = (sym ???? r).
notation ".= r" with precedence 55 for @{'trans $r}.
interpretation "trans1" 'trans r = (trans1 ????? r).
interpretation "trans" 'trans r = (trans ????? r).

record unary_morphism (A,B: setoid1) : Type0 ≝
 { fun_1:1> A → B;
   prop_1: ∀a,a'. eq1 ? a a' → eq1 ? (fun_1 a) (fun_1 a')
 }.

record binary_morphism (A,B,C:setoid) : Type0 ≝
 { fun:2> A → B → C;
   prop: ∀a,a',b,b'. eq ? a a' → eq ? b b' → eq ? (fun a b) (fun a' b')
 }.

record binary_morphism1 (A,B,C:setoid1) : Type0 ≝
 { fun1:2> A → B → C;
   prop1: ∀a,a',b,b'. eq1 ? a a' → eq1 ? b b' → eq1 ? (fun1 a b) (fun1 a' b')
 }.

notation "† c" with precedence 90 for @{'prop1 $c }.
notation "l ‡ r" with precedence 90 for @{'prop $l $r }.
notation "#" with precedence 90 for @{'refl}.
interpretation "prop_1" 'prop1 c = (prop_1 ????? c).
interpretation "prop1" 'prop l r = (prop1 ???????? l r).
interpretation "prop" 'prop l r = (prop ???????? l r).
interpretation "refl1" 'refl = (refl1 ???).
interpretation "refl" 'refl = (refl ???).

definition CPROP: setoid1.
 constructor 1;
  [ apply CProp
  | constructor 1;
     [ apply Iff
     | intros 1; split; intro; assumption
     | intros 3; cases H; split; assumption
     | intros 5; cases H; cases H1; split; intro;
        [ apply (H4 (H2 H6)) | apply (H3 (H5 H6))]]]
qed.

definition if': ∀A,B:CPROP. A = B → A → B.
 intros; apply (if ?? H); assumption.
qed.

notation ". r" with precedence 55 for @{'if $r}.
interpretation "if" 'if r = (if' ?? r).

definition and_morphism: binary_morphism1 CPROP CPROP CPROP.
 constructor 1;
  [ apply And
  | intros; split; intro; cases H2; split;
     [ apply (if ?? H a1)
     | apply (if ?? H1 b1)
     | apply (fi ?? H a1)
     | apply (fi ?? H1 b1)]]
qed.

interpretation "and_morphism" 'and a b = (fun1 ??? and_morphism a b).

definition or_morphism: binary_morphism1 CPROP CPROP CPROP.
 constructor 1;
  [ apply Or
  | intros; split; intro; cases H2; [1,3:left |2,4: right]
     [ apply (if ?? H a1)
     | apply (fi ?? H a1)
     | apply (if ?? H1 b1)
     | apply (fi ?? H1 b1)]]
qed.

interpretation "or_morphism" 'or a b = (fun1 ??? or_morphism a b).

definition if_morphism: binary_morphism1 CPROP CPROP CPROP.
 constructor 1;
  [ apply (λA,B. A → B)
  | intros; split; intros;
     [ apply (if ?? H1); apply H2; apply (fi ?? H); assumption
     | apply (fi ?? H1); apply H2; apply (if ?? H); assumption]]
qed.

(*
definition eq_morphism: ∀S:setoid. binary_morphism S S CPROP.
 intro;
 constructor 1;
  [ apply (eq_rel ? (eq S))
  | intros; split; intro;
     [ apply (.= H \sup -1);
       apply (.= H2);
       assumption
     | apply (.= H);
       apply (.= H2);
       apply (H1 \sup -1)]]
qed.
*)

record category : Type1 ≝
 { objs:> Type;
   arrows: objs → objs → setoid;
   id: ∀o:objs. arrows o o;
   comp: ∀o1,o2,o3. binary_morphism (arrows o1 o2) (arrows o2 o3) (arrows o1 o3);
   comp_assoc: ∀o1,o2,o3,o4. ∀a12,a23,a34.
    comp o1 o3 o4 (comp o1 o2 o3 a12 a23) a34 = comp o1 o2 o4 a12 (comp o2 o3 o4 a23 a34);
   id_neutral_left: ∀o1,o2. ∀a: arrows o1 o2. comp ??? (id o1) a = a;
   id_neutral_right: ∀o1,o2. ∀a: arrows o1 o2. comp ??? a (id o2) = a
 }.

record category1 : Type2 ≝
 { objs1:> Type;
   arrows1: objs1 → objs1 → setoid1;
   id1: ∀o:objs1. arrows1 o o;
   comp1: ∀o1,o2,o3. binary_morphism1 (arrows1 o1 o2) (arrows1 o2 o3) (arrows1 o1 o3);
   comp_assoc1: ∀o1,o2,o3,o4. ∀a12,a23,a34.
    comp1 o1 o3 o4 (comp1 o1 o2 o3 a12 a23) a34 = comp1 o1 o2 o4 a12 (comp1 o2 o3 o4 a23 a34);
   id_neutral_right1: ∀o1,o2. ∀a: arrows1 o1 o2. comp1 ??? (id1 o1) a = a;
   id_neutral_left1: ∀o1,o2. ∀a: arrows1 o1 o2. comp1 ??? a (id1 o2) = a
 }.

notation "'ASSOC'" with precedence 90 for @{'assoc}.
notation "'ASSOC1'" with precedence 90 for @{'assoc1}.

interpretation "category1 composition" 'compose x y = (fun1 ??? (comp1 ????) y x).
interpretation "category1 assoc" 'assoc1 = (comp_assoc1 ????????).
interpretation "category composition" 'compose x y = (fun ??? (comp ????) y x).
interpretation "category assoc" 'assoc = (comp_assoc ????????).

definition unary_morphism_setoid: setoid → setoid → setoid.
 intros;
 constructor 1;
  [ apply (unary_morphism s s1);
  | constructor 1;
     [ intros (f g); apply (∀a. f a = g a);
     | intros 1; simplify; intros; apply refl;
     | simplify; intros; apply sym; apply H;
     | simplify; intros; apply trans; [2: apply H; | skip | apply H1]]]
qed.

notation "hbox(a break ⇒ b)" right associative with precedence 20 for @{ 'Imply $a $b }.
interpretation "unary morphism" 'Imply a b = (unary_morphism_setoid a b).
interpretation "unary morphism" 'Imply a b = (unary_morphism a b).

definition SET: category1.
 constructor 1;
  [ apply setoid;
  | apply rule (λS,T.unary_morphism_setoid S T);
  | intros; constructor 1; [ apply (λx.x); | intros; assumption ]
  | intros; constructor 1; [ intros; constructor 1; [ apply (λx. c1 (c x)); | intros;
     apply († (†H));]
  | intros; whd; intros; simplify; whd in H1; whd in H;
    apply trans; [ apply (b (a' a1)); | lapply (prop_1 ?? b (a a1) (a' a1));
     [ apply Hletin | apply (H a1); ]  | apply H1; ]]
  | intros; whd; intros; simplify; apply refl;
  | intros; simplify; whd; intros; simplify; apply refl;
  | intros; simplify; whd; intros; simplify; apply refl;
  ]
qed.

definition setoid_OF_SET: objs1 SET → setoid.
 intros; apply o; qed.

coercion setoid_OF_SET.


definition prop_1_SET : 
 ∀A,B:SET.∀w:arrows1 SET A B.∀a,b:A.eq1 ? a b→eq1 ? (w a) (w b).
intros; apply (prop_1 A B w a b H);
qed.

interpretation "SET dagger" 'prop1 h = (prop_1_SET ? ? ? ? ? h).

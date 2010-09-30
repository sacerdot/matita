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

include "logic/connectives.ma".

inductive Or (A,B:CProp) : CProp ≝
 | Left : A → Or A B
 | Right : B → Or A B.

interpretation "constructive or" 'or x y = (Or x y).

inductive Or3 (A,B,C:CProp) : CProp ≝
 | Left3 : A → Or3 A B C
 | Middle3 : B → Or3 A B C
 | Right3 : C → Or3 A B C.

interpretation "constructive ternary or" 'or3 x y z= (Or3 x y z).

notation < "hvbox(a break ∨ b break ∨ c)" with precedence 35 for @{'or3 $a $b $c}.

inductive Or4 (A,B,C,D:CProp) : CProp ≝
 | Left3 : A → Or4 A B C D
 | Middle3 : B → Or4 A B C D
 | Right3 : C → Or4 A B C D
 | Extra3: D → Or4 A B C D.

interpretation "constructive ternary or" 'or4 x y z t = (Or4 x y z t).

notation < "hvbox(a break ∨ b break ∨ c break ∨ d)" with precedence 35 for @{'or4 $a $b $c $d}.

inductive And (A,B:CProp) : CProp ≝
 | Conj : A → B → And A B.
 
interpretation "constructive and" 'and x y = (And x y).

inductive And3 (A,B,C:CProp) : CProp ≝
 | Conj3 : A → B → C → And3 A B C.

notation < "hvbox(a break ∧ b break ∧ c)" with precedence 35 for @{'and3 $a $b $c}.
 
interpretation "constructive ternary and" 'and3 x y z = (And3 x y z).

inductive And4 (A,B,C,D:CProp) : CProp ≝
 | Conj4 : A → B → C → D → And4 A B C D.

notation < "hvbox(a break ∧ b break ∧ c break ∧ d)" with precedence 35 for @{'and4 $a $b $c $d}.
 
interpretation "constructive quaternary and" 'and4 x y z t = (And4 x y z t).

record Iff (A,B:CProp) : CProp ≝
 { if: A → B;
   fi: B → A
 }.
 
record Iff1 (A,B:CProp) : CProp ≝
 { if1: A → B;
   fi1: B → A
 }.
 
interpretation "logical iff" 'iff x y = (Iff x y).

notation "hvbox(a break ⇔ b)" right associative with precedence 25 for @{'iff1 $a $b}.
interpretation "logical iff type1" 'iff1 x y = (Iff1 x y).

inductive exT (A:Type) (P:A→CProp) : CProp ≝
  ex_introT: ∀w:A. P w → exT A P.

interpretation "CProp exists" 'exists x = (exT ? x).

notation "\ll term 19 a, break term 19 b \gg" 
with precedence 90 for @{'dependent_pair $a $b}.
interpretation "dependent pair" 'dependent_pair a b = (ex_introT ?? a b).

definition pi1exT ≝ λA,P.λx:exT A P.match x with [ex_introT x _ ⇒ x].

interpretation "exT \fst" 'pi1 = (pi1exT ? ?).
interpretation "exT \fst" 'pi1a x = (pi1exT ? ? x).
interpretation "exT \fst" 'pi1b x y = (pi1exT ? ? x y).

definition pi2exT ≝ 
  λA,P.λx:exT A P.match x return λx.P (pi1exT ? ? x) with [ex_introT _ p ⇒ p].

interpretation "exT \snd" 'pi2 = (pi2exT ? ?).
interpretation "exT \snd" 'pi2a x = (pi2exT ? ? x).
interpretation "exT \snd" 'pi2b x y = (pi2exT ? ? x y).

inductive exP (A:Type) (P:A→Prop) : CProp ≝
  ex_introP: ∀w:A. P w → exP A P.
  
interpretation "dependent pair for Prop" 'dependent_pair a b = 
  (ex_introP ?? a b).

interpretation "CProp exists for Prop" 'exists x = (exP ? x).

definition pi1exP ≝ λA,P.λx:exP A P.match x with [ex_introP x _ ⇒ x].

interpretation "exP \fst" 'pi1 = (pi1exP ? ?).
interpretation "exP \fst" 'pi1a x = (pi1exP ? ? x).
interpretation "exP \fst" 'pi1b x y = (pi1exP ? ? x y).

definition pi2exP ≝ 
  λA,P.λx:exP A P.match x return λx.P (pi1exP ?? x) with [ex_introP _ p ⇒ p].

interpretation "exP \snd" 'pi2 = (pi2exP ? ?).
interpretation "exP \snd" 'pi2a x = (pi2exP ? ? x).
interpretation "exP \snd" 'pi2b x y = (pi2exP ? ? x y).

inductive exT23 (A:Type) (P:A→CProp) (Q:A→CProp) (R:A→A→CProp) : CProp ≝
  ex_introT23: ∀w,p:A. P w → Q p → R w p → exT23 A P Q R.

definition pi1exT23 ≝
  λA,P,Q,R.λx:exT23 A P Q R.match x with [ex_introT23 x _ _ _ _ ⇒ x].

interpretation "exT2 \fst" 'pi1 = (pi1exT23 ? ? ? ?).
interpretation "exT2 \fst" 'pi1a x = (pi1exT23 ? ? ? ? x).
interpretation "exT2 \fst" 'pi1b x y = (pi1exT23 ? ? ? ? x y).

definition pi2exT23 ≝
  λA,P,Q,R.λx:exT23 A P Q R.match x with [ex_introT23 _ x _ _ _ ⇒ x].

interpretation "exT2 \snd" 'pi2 = (pi2exT23 ? ? ? ?).   
interpretation "exT2 \snd" 'pi2a x = (pi2exT23 ? ? ? ? x).
interpretation "exT2 \snd" 'pi2b x y = (pi2exT23 ? ? ? ? x y).

inductive exT2 (A:Type) (P,Q:A→CProp) : CProp ≝
  ex_introT2: ∀w:A. P w → Q w → exT2 A P Q.

definition Not : CProp → Prop ≝ λx:CProp.x → False.

interpretation "constructive not" 'not x = (Not x).
  
definition cotransitive ≝
 λC:Type.λlt:C→C→CProp.∀x,y,z:C. lt x y → lt x z ∨ lt z y. 

definition coreflexive ≝ λC:Type.λlt:C→C→CProp. ∀x:C. ¬ (lt x x).

definition symmetric ≝ λC:Type.λlt:C→C→CProp. ∀x,y:C.lt x y → lt y x.

definition antisymmetric ≝ λA:Type.λR:A→A→CProp.λeq:A→A→Prop.∀x:A.∀y:A.R x y→R y x→eq x y.

definition reflexive ≝ λA:Type.λR:A→A→CProp.∀x:A.R x x.

definition transitive ≝ λA:Type.λR:A→A→CProp.∀x,y,z:A.R x y → R y z → R x z.
 

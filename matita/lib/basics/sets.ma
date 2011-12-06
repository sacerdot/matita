(*
    ||M||  This file is part of HELM, an Hypertextual, Electronic        
    ||A||  Library of Mathematics, developed at the Computer Science     
    ||T||  Department of the University of Bologna, Italy.                     
    ||I||                                                                 
    ||T||  
    ||A||  This file is distributed under the terms of the 
    \   /  GNU General Public License Version 2        
     \ /      
      V_______________________________________________________________ *)

include "basics/logic.ma".

(**** a subset of A is just an object of type A→Prop ****)

definition empty_set ≝ λA:Type[0].λa:A.False.
notation "\emptyv" non associative with precedence 90 for @{'empty_set}.
interpretation "empty set" 'empty_set = (empty_set ?).

definition singleton ≝ λA.λx,a:A.x=a.
(* notation "{x}" non associative with precedence 90 for @{'sing_lang $x}. *)
interpretation "singleton" 'singl x = (singleton ? x).

definition union : ∀A:Type[0].∀P,Q.A → Prop ≝ λA,P,Q,a.P a ∨ Q a.
interpretation "union" 'union a b = (union ? a b).

definition intersection : ∀A:Type[0].∀P,Q.A→Prop ≝ λA,P,Q,a.P a ∧ Q a.
interpretation "intersection" 'intersects a b = (intersection ? a b).

definition subset: ∀A:Type[0].∀P,Q:A→Prop.Prop ≝ λA,P,Q.∀a:A.(P a → Q a).
interpretation "subset" 'subseteq a b = (intersection ? a b).

(* extensional equality *)
definition eqP ≝ λA:Type[0].λP,Q:A → Prop.∀a:A.P a ↔ Q a.
notation "A =1 B" non associative with precedence 45 for @{'eqP $A $B}.
interpretation "extensional equality" 'eqP a b = (eqP ? a b).

lemma eqP_sym: ∀U.∀A,B:U →Prop. 
  A =1 B → B =1 A.
#U #A #B #eqAB #a @iff_sym @eqAB qed.
 
lemma eqP_trans: ∀U.∀A,B,C:U →Prop. 
  A =1 B → B =1 C → A =1 C.
#U #A #B #C #eqAB #eqBC #a @iff_trans // qed.

lemma eqP_union_r: ∀U.∀A,B,C:U →Prop. 
  A =1 C  → A ∪ B =1 C ∪ B.
#U #A #B #C #eqAB #a @iff_or_r @eqAB qed.
  
lemma eqP_union_l: ∀U.∀A,B,C:U →Prop. 
  B =1 C  → A ∪ B =1 A ∪ C.
#U #A #B #C #eqBC #a @iff_or_l @eqBC qed.
  
(* set equalities *)
lemma union_comm : ∀U.∀A,B:U →Prop. 
  A ∪ B =1 B ∪ A.
#U #A #B #a % * /2/ qed. 

lemma union_assoc: ∀U.∀A,B,C:U → Prop. 
  A ∪ B ∪ C =1 A ∪ (B ∪ C).
#S #A #B #C #w % [* [* /3/ | /3/] | * [/3/ | * /3/]
qed.   

lemma cap_comm : ∀U.∀A,B:U →Prop. 
  A ∩ B =1 B ∩ A.
#U #A #B #a % * /2/ qed. 

lemma union_idemp: ∀U.∀A:U →Prop. 
  A ∪ A =1 A.
#U #A #a % [* // | /2/] qed. 

lemma cap_idemp: ∀U.∀A:U →Prop. 
  A ∩ A =1 A.
#U #A #a % [* // | /2/] qed. 



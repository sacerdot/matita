(*
    ||M||  This file is part of HELM, an Hypertextual, Electronic        
    ||A||  Library of Mathematics, developed at the Computer Science     
    ||T||  Department of the University of Bologna, Italy.                     
    ||I||                                                                 
    ||T||  
    ||A||  
    \   /  This file is distributed under the terms of the       
     \ /   GNU General Public License Version 2   
      V_______________________________________________________________ *)

include "basics/relations.ma".

(********** bool **********)
inductive bool: Type[0] ≝ 
  | true : bool
  | false : bool.

theorem not_eq_true_false : true ≠ false.
@nmk #Heq destruct
qed.

definition notb : bool → bool ≝
λ b:bool. match b with [true ⇒ false|false ⇒ true ].

interpretation "boolean not" 'not x = (notb x).

theorem notb_elim: ∀ b:bool.∀ P:bool → Prop.
match b with
[ true ⇒ P false
| false ⇒ P true] → P (notb b).
#b #P elim b normalize // qed.

theorem notb_notb: ∀b:bool. notb (notb b) = b.
#b elim b // qed.

theorem injective_notb: injective bool bool notb.
#b1 #b2 #H // qed.

definition andb : bool → bool → bool ≝
λb1,b2:bool. match b1 with [ true ⇒ b2 | false ⇒ false ].

interpretation "boolean and" 'and x y = (andb x y).

theorem andb_elim: ∀ b1,b2:bool. ∀ P:bool → Prop.
match b1 with [ true ⇒ P b2 | false ⇒ P false] → P (b1 ∧ b2).
#b1 #b2 #P (elim b1) normalize // qed.

theorem andb_true_l: ∀ b1,b2. (b1 ∧ b2) = true → b1 = true.
#b1 (cases b1) normalize // qed.

theorem andb_true_r: ∀b1,b2. (b1 ∧ b2) = true → b2 = true.
#b1 #b2 (cases b1) normalize // (cases b2) // qed.

theorem andb_true: ∀b1,b2. (b1 ∧ b2) = true → b1 = true ∧ b2 = true.
/3/ qed.

definition orb : bool → bool → bool ≝
λb1,b2:bool.match b1 with [ true ⇒ true | false ⇒ b2].
 
interpretation "boolean or" 'or x y = (orb x y).

theorem orb_elim: ∀ b1,b2:bool. ∀ P:bool → Prop.
match b1 with [ true ⇒ P true | false ⇒ P b2] → P (orb b1 b2).
#b1 #b2 #P (elim b1) normalize // qed.

lemma orb_true_r1: ∀b1,b2:bool. 
  b1 = true → (b1 ∨ b2) = true.
#b1 #b2 #H >H // qed.

lemma orb_true_r2: ∀b1,b2:bool. 
  b2 = true → (b1 ∨ b2) = true.
#b1 #b2 #H >H cases b1 // qed.

lemma orb_true_l: ∀b1,b2:bool. 
  (b1 ∨ b2) = true → (b1 = true) ∨ (b2 = true).
* normalize /2/ qed.

definition if_then_else: ∀A:Type[0]. bool → A → A → A ≝ 
λA.λb.λ P,Q:A. match b with [ true ⇒ P | false  ⇒ Q].

notation "'if' term 19 e 'then' term 19 t 'else' term 19 f" non associative with precedence 19 for @{ 'if_then_else $e $t $f }.
interpretation "if_then_else" 'if_then_else e t f = (if_then_else ? e t f).

theorem bool_to_decidable_eq: 
  ∀b1,b2:bool. decidable (b1=b2).
#b1 #b2 (cases b1) (cases b2) /2/ %2 /3/ qed.

theorem true_or_false:
∀b:bool. b = true ∨ b = false.
#b (cases b) /2/ qed.


(****** DeqSet: a set with a decidbale equality ******)

record DeqSet : Type[1] ≝ { carr :> Type[0];
   eqb: carr → carr → bool;
   eqb_true: ∀x,y. (eqb x y = true) ↔ (x = y)
}.

notation "a == b" non associative with precedence 45 for @{ 'eqb $a $b }.
interpretation "eqb" 'eqb a b = (eqb ? a b).


(****** EnumSet: a DeqSet with an enumeration function  ******

record EnumSet : Type[1] ≝ { carr :> DeqSet;
   enum: carr 
   eqb_true: ∀x,y. (eqb x y = true) ↔ (x = y)
}.

*)
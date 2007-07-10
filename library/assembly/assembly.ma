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

set "baseuri" "cic:/matita/assembly/".

include "nat/div_and_mod.ma".
include "list/list.ma".

inductive exadecimal : Type ≝
   x0: exadecimal
 | x1: exadecimal
 | x2: exadecimal
 | x3: exadecimal
 | x4: exadecimal
 | x5: exadecimal
 | x6: exadecimal
 | x7: exadecimal
 | x8: exadecimal
 | x9: exadecimal
 | xA: exadecimal
 | xB: exadecimal
 | xC: exadecimal
 | xD: exadecimal
 | xE: exadecimal
 | xF: exadecimal.
 
record byte : Type ≝ {
 bh: exadecimal;
 bl: exadecimal
}.

definition eqex ≝
 λb1,b2.
  match b1 with
   [ x0 ⇒
       match b2 with
        [ x0 ⇒ true  | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false
        | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
        | x8 ⇒ false | x9 ⇒ false | xA ⇒ false | xB ⇒ false
        | xC ⇒ false | xD ⇒ false | xE ⇒ false | xF ⇒ false ] 
   | x1 ⇒
       match b2 with
        [ x0 ⇒ false | x1 ⇒ true  | x2 ⇒ false | x3 ⇒ false
        | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
        | x8 ⇒ false | x9 ⇒ false | xA ⇒ false | xB ⇒ false
        | xC ⇒ false | xD ⇒ false | xE ⇒ false | xF ⇒ false ] 
   | x2 ⇒
       match b2 with
        [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ true  | x3 ⇒ false
        | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
        | x8 ⇒ false | x9 ⇒ false | xA ⇒ false | xB ⇒ false
        | xC ⇒ false | xD ⇒ false | xE ⇒ false | xF ⇒ false ] 
   | x3 ⇒
       match b2 with
        [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ true 
        | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
        | x8 ⇒ false | x9 ⇒ false | xA ⇒ false | xB ⇒ false
        | xC ⇒ false | xD ⇒ false | xE ⇒ false | xF ⇒ false ] 
   | x4 ⇒
       match b2 with
        [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false
        | x4 ⇒ true  | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
        | x8 ⇒ false | x9 ⇒ false | xA ⇒ false | xB ⇒ false
        | xC ⇒ false | xD ⇒ false | xE ⇒ false | xF ⇒ false ] 
   | x5 ⇒
       match b2 with
        [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false
        | x4 ⇒ false | x5 ⇒ true  | x6 ⇒ false | x7 ⇒ false
        | x8 ⇒ false | x9 ⇒ false | xA ⇒ false | xB ⇒ false
        | xC ⇒ false | xD ⇒ false | xE ⇒ false | xF ⇒ false ] 
   | x6 ⇒
       match b2 with
        [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false
        | x4 ⇒ false | x5 ⇒ false | x6 ⇒ true  | x7 ⇒ false
        | x8 ⇒ false | x9 ⇒ false | xA ⇒ false | xB ⇒ false
        | xC ⇒ false | xD ⇒ false | xE ⇒ false | xF ⇒ false ] 
   | x7 ⇒
       match b2 with
        [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false
        | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ true 
        | x8 ⇒ false | x9 ⇒ false | xA ⇒ false | xB ⇒ false
        | xC ⇒ false | xD ⇒ false | xE ⇒ false | xF ⇒ false ] 
   | x8 ⇒
       match b2 with
        [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false
        | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
        | x8 ⇒ true  | x9 ⇒ false | xA ⇒ false | xB ⇒ false
        | xC ⇒ false | xD ⇒ false | xE ⇒ false | xF ⇒ false ] 
   | x9 ⇒
       match b2 with
        [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false
        | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
        | x8 ⇒ false | x9 ⇒ true  | xA ⇒ false | xB ⇒ false
        | xC ⇒ false | xD ⇒ false | xE ⇒ false | xF ⇒ false ] 
   | xA ⇒
       match b2 with
        [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false
        | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
        | x8 ⇒ false | x9 ⇒ false | xA ⇒ true  | xB ⇒ false
        | xC ⇒ false | xD ⇒ false | xE ⇒ false | xF ⇒ false ] 
   | xB ⇒
       match b2 with
        [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false
        | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
        | x8 ⇒ false | x9 ⇒ false | xA ⇒ false | xB ⇒ true 
        | xC ⇒ false | xD ⇒ false | xE ⇒ false | xF ⇒ false ] 
   | xC ⇒
       match b2 with
        [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false
        | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
        | x8 ⇒ false | x9 ⇒ false | xA ⇒ false | xB ⇒ false
        | xC ⇒ true  | xD ⇒ false | xE ⇒ false | xF ⇒ false ] 
   | xD ⇒
       match b2 with
        [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false
        | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
        | x8 ⇒ false | x9 ⇒ false | xA ⇒ false | xB ⇒ false
        | xC ⇒ false | xD ⇒ true  | xE ⇒ false | xF ⇒ false ] 
   | xE ⇒
       match b2 with
        [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false
        | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
        | x8 ⇒ false | x9 ⇒ false | xA ⇒ false | xB ⇒ false
        | xC ⇒ false | xD ⇒ false | xE ⇒ true  | xF ⇒ false ] 
   | xF ⇒
       match b2 with
        [ x0 ⇒ false | x1 ⇒ false | x2 ⇒ false | x3 ⇒ false
        | x4 ⇒ false | x5 ⇒ false | x6 ⇒ false | x7 ⇒ false
        | x8 ⇒ false | x9 ⇒ false | xA ⇒ false | xB ⇒ false
        | xC ⇒ false | xD ⇒ false | xE ⇒ false | xF ⇒ true  ]]. 


definition eqbyte ≝
 λb,b'. eqex (bh b) (bh b') ∧ eqex (bl b) (bl b').

alias num (instance 0) = "natural number".
definition nat_of_exadecimal ≝
 λb.
  match b with
   [ x0 ⇒ 0
   | x1 ⇒ 1
   | x2 ⇒ 2
   | x3 ⇒ 3
   | x4 ⇒ 4
   | x5 ⇒ 5
   | x6 ⇒ 6
   | x7 ⇒ 7
   | x8 ⇒ 8
   | x9 ⇒ 9
   | xA ⇒ 10
   | xB ⇒ 11
   | xC ⇒ 12
   | xD ⇒ 13
   | xE ⇒ 14
   | xF ⇒ 15
   ].

coercion cic:/matita/assembly/nat_of_exadecimal.con.

definition nat_of_byte ≝ λb:byte. 16*(bh b) + (bl b).

coercion cic:/matita/assembly/nat_of_byte.con.

let rec exadecimal_of_nat b ≝
  match b with [ O ⇒ x0 | S b ⇒
  match b with [ O ⇒ x1 | S b ⇒
  match b with [ O ⇒ x2 | S b ⇒ 
  match b with [ O ⇒ x3 | S b ⇒ 
  match b with [ O ⇒ x4 | S b ⇒ 
  match b with [ O ⇒ x5 | S b ⇒ 
  match b with [ O ⇒ x6 | S b ⇒ 
  match b with [ O ⇒ x7 | S b ⇒ 
  match b with [ O ⇒ x8 | S b ⇒ 
  match b with [ O ⇒ x9 | S b ⇒ 
  match b with [ O ⇒ xA | S b ⇒ 
  match b with [ O ⇒ xB | S b ⇒ 
  match b with [ O ⇒ xC | S b ⇒ 
  match b with [ O ⇒ xD | S b ⇒ 
  match b with [ O ⇒ xE | S b ⇒ 
  match b with [ O ⇒ xF | S b ⇒ exadecimal_of_nat b ]]]]]]]]]]]]]]]]. 

definition byte_of_nat ≝
 λn. mk_byte (exadecimal_of_nat (n / 16)) (exadecimal_of_nat n).

lemma byte_of_nat_nat_of_byte: ∀b. byte_of_nat (nat_of_byte b) = b.
 intros;
 elim b;
 elim e;
 elim e1;
 reflexivity.
qed.

notation "14" non associative with precedence 80 for @{ 'x14 }.
interpretation "natural number" 'x14 = 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/1)))))))))))))))).

notation "22" non associative with precedence 80 for @{ 'x22 }.
interpretation "natural number" 'x22 = 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/1)))))))))))))))))))))))).
 
notation "256" non associative with precedence 80 for @{ 'x256 }.
interpretation "natural number" 'x256 = 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/2) 
(cic:/matita/nat/nat/nat.ind#xpointer(1/1/1) 
))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

(*
lemma sign_ok: ∀ n:nat. nat_of_byte (byte_of_nat n) = n \mod 256.
 intros; elim n; [ reflexivity | unfold byte_of_nat. 
qed.
*)

definition addr ≝ nat.

definition xpred ≝
 λb.
  match b with
   [ x0 ⇒ xF
   | x1 ⇒ x0
   | x2 ⇒ x1
   | x3 ⇒ x2
   | x4 ⇒ x3
   | x5 ⇒ x4
   | x6 ⇒ x5
   | x7 ⇒ x6
   | x8 ⇒ x7
   | x9 ⇒ x8
   | xA ⇒ x9
   | xB ⇒ xA
   | xC ⇒ xB
   | xD ⇒ xC
   | xE ⇒ xD
   | xF ⇒ xE ].

definition bpred ≝
 λb.
  match eqex (bl b) x0 with
   [ true ⇒ mk_byte (xpred (bh b)) (xpred (bl b))
   | false ⇒ mk_byte (bh b) (xpred (bl b))
   ]. 

(* Way too slow and subsumed by previous theorem
lemma bpred_pred:
 ∀b.
  match eqbyte b (mk_byte x0 x0) with
   [ true ⇒ nat_of_byte (bpred b) = mk_byte xF xF
   | false ⇒ nat_of_byte (bpred b) = pred (nat_of_byte b)].
 intros;
 elim b;
 elim e;
 elim e1;
 reflexivity.
qed.
*)

definition addr_of_byte : byte → addr ≝ λb. nat_of_byte b.

coercion cic:/matita/assembly/addr_of_byte.con.

inductive opcode: Type ≝
   ADDd: opcode  (* 3 clock, 171 *)
 | BEQ: opcode   (* 3, 55 *)
 | BRA: opcode   (* 3, 48 *)
 | DECd: opcode  (* 5, 58 *)
 | LDAi: opcode  (* 2, 166 *)
 | LDAd: opcode  (* 3, 182 *)
 | STAd: opcode. (* 3, 183 *)

let rec cycles_of_opcode op : nat ≝
 match op with
  [ ADDd ⇒ 3
  | BEQ ⇒ 3
  | BRA ⇒ 3
  | DECd ⇒ 5
  | LDAi ⇒ 2
  | LDAd ⇒ 3
  | STAd ⇒ 3
  ].

inductive cartesian_product (A,B: Type) : Type ≝
 couple: ∀a:A.∀b:B. cartesian_product A B.

definition opcodemap ≝
 [ couple ? ? ADDd (mk_byte xA xB);
   couple ? ? BEQ (mk_byte x3 x7);
   couple ? ? BRA (mk_byte x3 x0);
   couple ? ? DECd (mk_byte x3 xA);
   couple ? ? LDAi (mk_byte xA x6);
   couple ? ? LDAd (mk_byte xB x6);
   couple ? ? STAd (mk_byte xB x7) ].

definition opcode_of_byte ≝
 λb.
  let rec aux l ≝
   match l with
    [ nil ⇒ ADDd
    | cons c tl ⇒
       match c with
        [ couple op n ⇒
           match eqbyte n b with
            [ true ⇒ op
            | false ⇒ aux tl
            ]]]
  in
   aux opcodemap.

definition magic_of_opcode ≝
 λop1.
  match op1 with
   [ ADDd ⇒ 0
   | BEQ ⇒  1 
   | BRA ⇒  2
   | DECd ⇒ 3
   | LDAi ⇒ 4
   | LDAd ⇒ 5
   | STAd ⇒ 6 ].
   
definition opcodeeqb ≝
 λop1,op2. eqb (magic_of_opcode op1) (magic_of_opcode op2).

definition byte_of_opcode : opcode → byte ≝
 λop.
  let rec aux l ≝
   match l with
    [ nil ⇒ mk_byte x0 x0
    | cons c tl ⇒
       match c with
        [ couple op' n ⇒
           match opcodeeqb op op' with
            [ true ⇒ n
            | false ⇒ aux tl
            ]]]
  in
   aux opcodemap.

record status : Type ≝ {
  acc : byte;
  pc  : addr;
  spc : addr;
  zf  : bool;
  cf  : bool;
  mem : addr → byte;
  clk : nat
}.

definition update ≝
 λf: addr → byte.λa.λv.λx.
  match eqb x a with
   [ true ⇒ v
   | false ⇒ f x ].

definition mmod16 ≝ λn. nat_of_byte (byte_of_nat n).

definition tick ≝
 λs:status.
  (* fetch *)
  let opc ≝ opcode_of_byte (mem s (pc s)) in
  let op1 ≝ mem s (S (pc s)) in
  let clk' ≝ cycles_of_opcode opc in
  match eqb (S (clk s)) clk' with
   [ true ⇒
      match opc with
       [ ADDd ⇒
          let x ≝ nat_of_byte (mem s op1) in
          let acc' ≝ acc s + x in (* signed!!! *)
           mk_status (byte_of_nat acc') (2 + pc s) (spc s)
            (eqb O acc') (cf s) (mem s) 0
       | BEQ ⇒
          mk_status
           (acc s)
           (match zf s with
             [ true ⇒ mmod16 (2 + op1 + pc s) (*\mod 256*)   (* signed!!! *)
             | false ⇒ 2 + pc s
             ])
           (spc s)
           (zf s)
           (cf s)
           (mem s)
           0
       | BRA ⇒
          mk_status
           (acc s) (mmod16 (2 + op1 + pc s) (*\mod 256*)) (* signed!!! *)
           (spc s)
           (zf s)
           (cf s)
           (mem s)
           0
       | DECd ⇒
          let x ≝ bpred (mem s op1) in (* signed!!! *)
          let mem' ≝ update (mem s) op1 x in
           mk_status (acc s) (2 + pc s) (spc s)
            (eqb O x) (cf s) mem' 0 (* check zb!!! *)
       | LDAi ⇒
          mk_status op1 (2 + pc s) (spc s) (eqb O op1) (cf s) (mem s) 0
       | LDAd ⇒
          let x ≝ mem s op1 in
           mk_status x (2 + pc s) (spc s) (eqb O x) (cf s) (mem s) 0
       | STAd ⇒
          mk_status (acc s) (2 + pc s) (spc s) (zf s) (cf s)
           (update (mem s) op1 (acc s)) 0
       ]
   | false ⇒
       mk_status
        (acc s) (pc s) (spc s) (zf s) (cf s) (mem s) (S (clk s))
   ].

let rec execute s n on n ≝
 match n with
  [ O ⇒ s
  | S n' ⇒ execute (tick s) n'
  ].
  
lemma foo: ∀s,n. execute s (S n) = execute (tick s) n.
 intros; reflexivity.
qed.

notation "hvbox(# break a)"
  non associative with precedence 80
for @{ 'byte_of_opcode $a }.
interpretation "byte_of_opcode" 'byte_of_opcode a =
 (cic:/matita/assembly/byte_of_opcode.con a).

definition mult_source : list byte ≝
  [#LDAi; mk_byte x0 x0; (* A := 0 *)
   #STAd; mk_byte x2 x0; (* Z := A *)
   #LDAd; mk_byte x1 xF; (* (l1) A := Y *)
   #BEQ;  mk_byte x0 xA; (* if A == 0 then goto l2 *)
   #LDAd; mk_byte x2 x0; (* A := Z *)
   #DECd; mk_byte x1 xF; (* Y := Y - 1 *)
   #ADDd; mk_byte x1 xE; (* A += X *)
   #STAd; mk_byte x2 x0; (* Z := A *)
   #BRA;  mk_byte xF x2; (* goto l1 *)
   #LDAd; mk_byte x2 x0].(* (l2) *)

definition mult_status ≝
 λx,y.
  mk_status (mk_byte x0 x0) 0 0 false false
   (λa:addr.
     match leb a 29 with
      [ true ⇒ nth ? mult_source (mk_byte x0 x0) a
      | false ⇒
         match eqb a 30 with
          [ true ⇒ x
          | false ⇒ y
          ]
      ]) 0.

(*
lemma foobar:
 ∀x.
  let y ≝ mk_byte x0 x1 in
  let i ≝ 14 + 23 * nat_of_byte y in
  let s ≝ execute (mult_status x y) i in
   pc s = 20 ∧ mem s 32 = x.
 intros;
 letin w ≝ 22;
 letin opc ≝ (let s ≝ execute (mult_status x y) w in opcode_of_byte (mem s (pc s))); whd in opc;
 letin acc' ≝ (acc (execute (mult_status x y) w)); change in acc' with (byte_of_nat x);
 letin z ≝ (let s ≝ (execute (mult_status x y) w) in mem s 32); whd in z;
 letin x ≝ (let s ≝ (execute (mult_status x y) w) in mem s 30); whd in x;
 (*letin xxx ≝ (byte_of_nat (x+y)); normalize in xxx;*)
 split;
  [ normalize; reflexivity
  | change with (byte_of_nat x = x);
 normalize;
 split;
  [ reflexivity
  | change with (byte_of_nat (x + 0));
 letin www ≝ (nat_of_byte (byte_of_nat 260)); whd in www;
 letin xxx ≝ (260 \mod 256); reduce in xxx;
 letin xxx ≝ ((18 + 242) \mod 256);
 whd in xxx;
 letin pc' ≝ (pc s);
 normalize in pc';
 letin opcode ≝ (let s ≝ s in opcode_of_byte (mem s (pc s)));
 normalize in opcode;
 csc.
 split;
 reduce in s;
 reflexivity.
qed.

lemma goo1:
 ∀x,y.
  let i ≝ 14 + 23 * nat_of_byte y in
  let s ≝ execute (mult_status x y) i in
   pc s = 22 ∧ mem s 32 = byte_of_nat (nat_of_byte x * nat_of_byte y).
 intros;
qed.

lemma goo: True.
 letin s0 ≝ mult_status;
 letin pc0 ≝ (pc s0); 
 reduce in pc0;
 letin i0 ≝ (opcode_of_byte (mem s0 pc0));
 reduce in i0;
 
 letin s1 ≝ (execute s0 (cycles_of_opcode i0));
 letin pc1 ≝ (pc s1);
 reduce in pc1;
 letin i1 ≝ (opcode_of_byte (mem s1 pc1));
 reduce in i1;

 letin s2 ≝ (execute s1 (cycles_of_opcode i1));
 letin pc2 ≝ (pc s2);
 reduce in pc2;
 letin i2 ≝ (opcode_of_byte (mem s2 pc2));
 reduce in i2;

 letin s3 ≝ (execute s2 (cycles_of_opcode i2));
 letin pc3 ≝ (pc s3);
 reduce in pc3;
 letin i3 ≝ (opcode_of_byte (mem s3 pc3));
 reduce in i3;
 letin zf3 ≝ (zf s3);
 reduce in zf3;

 letin s4 ≝ (execute s3 (cycles_of_opcode i3));
 letin pc4 ≝ (pc s4);
 reduce in pc4;
 letin i4 ≝ (opcode_of_byte (mem s4 pc4));
 reduce in i4;

 letin s5 ≝ (execute s4 (cycles_of_opcode i4));
 letin pc5 ≝ (pc s5);
 reduce in pc5;
 letin i5 ≝ (opcode_of_byte (mem s5 pc5));
 reduce in i5;
 
 letin s6 ≝ (execute s5 (cycles_of_opcode i5));
 letin pc6 ≝ (pc s6);
 reduce in pc6;
 letin i6 ≝ (opcode_of_byte (mem s6 pc6));
 reduce in i6;
 
 letin s7 ≝ (execute s6 (cycles_of_opcode i6));
 letin pc7 ≝ (pc s7);
 reduce in pc7;
 letin i7 ≝ (opcode_of_byte (mem s7 pc7));
 reduce in i7;
 
 letin s8 ≝ (execute s7 (cycles_of_opcode i7));
 letin pc8 ≝ (pc s8);
 reduce in pc8;
 letin i8 ≝ (opcode_of_byte (mem s8 pc8));
 reduce in i8;

 letin s9 ≝ (execute s8 (cycles_of_opcode i8));
 letin pc9 ≝ (pc s9);
 reduce in pc9;
 letin i9 ≝ (opcode_of_byte (mem s9 pc9));
 reduce in i9;
 
 exact I.
qed.
*)
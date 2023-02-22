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

(* ********************************************************************** *)
(*                          Progetto FreeScale                            *)
(*                                                                        *)
(*   Sviluppato da: Ing. Cosimo Oliboni, oliboni@cs.unibo.it              *)
(*   Sviluppo: 2008-2010                                                  *)
(*                                                                        *)
(* ********************************************************************** *)

include "num/bool.ma".

(* ******** *)
(* NATURALI *)
(* ******** *)

ninductive nat : Type ≝
  O : nat
| S : nat → nat.

(*
interpretation "Natural numbers" 'N = nat.

default "natural numbers" cic:/matita/common/nat/nat.ind.

alias num (instance 0) = "natural number".
*)

nlet rec nat_it (T:Type) (f:T → T) (arg:T) (n:nat) on n ≝
 match n with
  [ O ⇒ arg
  | S n' ⇒ nat_it T f (f arg) n'
  ].

ndefinition nat1 ≝ S O.
ndefinition nat2 ≝ S nat1.
ndefinition nat3 ≝ S nat2.
ndefinition nat4 ≝ S nat3.
ndefinition nat5 ≝ S nat4.
ndefinition nat6 ≝ S nat5.
ndefinition nat7 ≝ S nat6.
ndefinition nat8 ≝ S nat7.
ndefinition nat9 ≝ S nat8.
ndefinition nat10 ≝ S nat9.
ndefinition nat11 ≝ S nat10.
ndefinition nat12 ≝ S nat11.
ndefinition nat13 ≝ S nat12.
ndefinition nat14 ≝ S nat13.
ndefinition nat15 ≝ S nat14.
ndefinition nat16 ≝ S nat15.
ndefinition nat17 ≝ S nat16.
ndefinition nat18 ≝ S nat17.
ndefinition nat19 ≝ S nat18.
ndefinition nat20 ≝ S nat19.
ndefinition nat21 ≝ S nat20.
ndefinition nat22 ≝ S nat21.
ndefinition nat23 ≝ S nat22.
ndefinition nat24 ≝ S nat23.
ndefinition nat25 ≝ S nat24.
ndefinition nat26 ≝ S nat25.
ndefinition nat27 ≝ S nat26.
ndefinition nat28 ≝ S nat27.
ndefinition nat29 ≝ S nat28.
ndefinition nat30 ≝ S nat29.
ndefinition nat31 ≝ S nat30.
ndefinition nat32 ≝ S nat31.
ndefinition nat33 ≝ S nat32.
ndefinition nat34 ≝ S nat33.
ndefinition nat35 ≝ S nat34.
ndefinition nat36 ≝ S nat35.
ndefinition nat37 ≝ S nat36.
ndefinition nat38 ≝ S nat37.
ndefinition nat39 ≝ S nat38.
ndefinition nat40 ≝ S nat39.
ndefinition nat41 ≝ S nat40.
ndefinition nat42 ≝ S nat41.
ndefinition nat43 ≝ S nat42.
ndefinition nat44 ≝ S nat43.
ndefinition nat45 ≝ S nat44.
ndefinition nat46 ≝ S nat45.
ndefinition nat47 ≝ S nat46.
ndefinition nat48 ≝ S nat47.
ndefinition nat49 ≝ S nat48.
ndefinition nat50 ≝ S nat49.
ndefinition nat51 ≝ S nat50.
ndefinition nat52 ≝ S nat51.
ndefinition nat53 ≝ S nat52.
ndefinition nat54 ≝ S nat53.
ndefinition nat55 ≝ S nat54.
ndefinition nat56 ≝ S nat55.
ndefinition nat57 ≝ S nat56.
ndefinition nat58 ≝ S nat57.
ndefinition nat59 ≝ S nat58.
ndefinition nat60 ≝ S nat59.
ndefinition nat61 ≝ S nat60.
ndefinition nat62 ≝ S nat61.
ndefinition nat63 ≝ S nat62.
ndefinition nat64 ≝ S nat63.
ndefinition nat65 ≝ S nat64.
ndefinition nat66 ≝ S nat65.
ndefinition nat67 ≝ S nat66.
ndefinition nat68 ≝ S nat67.
ndefinition nat69 ≝ S nat68.
ndefinition nat70 ≝ S nat69.
ndefinition nat71 ≝ S nat70.
ndefinition nat72 ≝ S nat71.
ndefinition nat73 ≝ S nat72.
ndefinition nat74 ≝ S nat73.
ndefinition nat75 ≝ S nat74.
ndefinition nat76 ≝ S nat75.
ndefinition nat77 ≝ S nat76.
ndefinition nat78 ≝ S nat77.
ndefinition nat79 ≝ S nat78.
ndefinition nat80 ≝ S nat79.
ndefinition nat81 ≝ S nat80.
ndefinition nat82 ≝ S nat81.
ndefinition nat83 ≝ S nat82.
ndefinition nat84 ≝ S nat83.
ndefinition nat85 ≝ S nat84.
ndefinition nat86 ≝ S nat85.
ndefinition nat87 ≝ S nat86.
ndefinition nat88 ≝ S nat87.
ndefinition nat89 ≝ S nat88.
ndefinition nat90 ≝ S nat89.
ndefinition nat91 ≝ S nat90.
ndefinition nat92 ≝ S nat91.
ndefinition nat93 ≝ S nat92.
ndefinition nat94 ≝ S nat93.
ndefinition nat95 ≝ S nat94.
ndefinition nat96 ≝ S nat95.
ndefinition nat97 ≝ S nat96.
ndefinition nat98 ≝ S nat97.
ndefinition nat99 ≝ S nat98.
ndefinition nat100 ≝ S nat99.

nlet rec eq_nat (n1,n2:nat) on n1 ≝
 match n1 with
  [ O ⇒ match n2 with [ O ⇒ true | S _ ⇒ false ]
  | S n1' ⇒ match n2 with [ O ⇒ false | S n2' ⇒ eq_nat n1' n2' ]
  ].

nlet rec le_nat n m ≝ 
 match n with 
  [ O ⇒ true
  | (S p) ⇒ match m with 
   [ O ⇒ false | (S q) ⇒ le_nat p q ]
  ].

interpretation "natural 'less or equal to'" 'leq x y = (le_nat x y).

ndefinition lt_nat ≝ λn1,n2:nat.(le_nat n1 n2) ⊗ (⊖ (eq_nat n1 n2)).

interpretation "natural 'less than'" 'lt x y = (lt_nat x y).

ndefinition ge_nat ≝ λn1,n2:nat.(⊖ (le_nat n1 n2)) ⊕ (eq_nat n1 n2).

interpretation "natural 'greater or equal to'" 'geq x y = (ge_nat x y).

ndefinition gt_nat ≝ λn1,n2:nat.⊖ (le_nat n1 n2).

interpretation "natural 'greater than'" 'gt x y = (gt_nat x y).

nlet rec plus (n1,n2:nat) on n1 ≝ 
 match n1 with
  [ O ⇒ n2
  | (S n1') ⇒ S (plus n1' n2) ].

interpretation "natural plus" 'plus x y = (plus x y).

nlet rec times (n1,n2:nat) on n1 ≝ 
 match n1 with 
  [ O ⇒ O
  | (S n1') ⇒ n2 + (times n1' n2) ].

interpretation "natural times" 'times x y = (times x y).

nlet rec minus n m ≝ 
 match n with 
 [ O ⇒ O
 | (S p) ⇒ 
	match m with
	[O ⇒ (S p)
  | (S q) ⇒ minus p q ]].

interpretation "natural minus" 'minus x y = (minus x y).

nlet rec div_aux p m n : nat ≝
match (le_nat m n) with
[ true ⇒ O
| false ⇒
  match p with
  [ O ⇒ O
  | (S q) ⇒ S (div_aux q (m-(S n)) n)]].

ndefinition div : nat → nat → nat ≝
λn,m.match m with 
 [ O ⇒ S n
 | (S p) ⇒ div_aux n n p]. 

interpretation "natural divide" 'divide x y = (div x y).

ndefinition pred ≝ λn.match n with [ O ⇒ O | S n ⇒ n ].

ndefinition nat128 ≝ nat64 + nat64.
ndefinition nat256 ≝ nat128 + nat128.
ndefinition nat512 ≝ nat256 + nat256.
ndefinition nat1024 ≝ nat512 + nat512.
ndefinition nat2048 ≝ nat1024 + nat1024.
ndefinition nat4096 ≝ nat2048 + nat2048.
ndefinition nat8192 ≝ nat4096 + nat4096.
ndefinition nat16384 ≝ nat8192 + nat8192.
ndefinition nat32768 ≝ nat16384 + nat16384.
ndefinition nat65536 ≝ nat32768 + nat32768.

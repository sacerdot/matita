include "logic/equality.ma".

(* Inclusion of: COL067-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : COL067-1 : TPTP v3.7.0. Released v1.2.0. *)

(*  Domain   : Combinatory Logic *)

(*  Problem  : Strong fixed point for B and S *)

(*  Version  : [WM88] (equality) axioms. *)

(*  English  : The strong fixed point property holds for the set  *)

(*             P consisting of the combinators B and S, where ((Sx)y)z  *)

(*             = (xz)(yz), ((Bx)y)z = x(yz). *)

(*  Refs     : [WM88]  Wos & McCune (1988), Challenge Problems Focusing on Eq *)

(*           : [Wos93] Wos (1993), The Kernel Strategy and Its Use for the St *)

(*  Source   : [Wos93] *)

(*  Names    : Question 4 [Wos93] *)

(*           : Question 5 [Wos93] *)

(*  Status   : Unknown *)

(*  Rating   : 1.00 v2.0.0 *)

(*  Syntax   : Number of clauses     :    3 (   0 non-Horn;   3 unit;   1 RR) *)

(*             Number of atoms       :    3 (   3 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    4 (   2 constant; 0-2 arity) *)

(*             Number of variables   :    7 (   0 singleton) *)

(*             Maximal term depth    :    4 (   4 average) *)

(*  Comments :  *)

(* -------------------------------------------------------------------------- *)
ntheorem prove_fixed_point:
 (∀Univ:Type.∀X:Univ.∀Y:Univ.∀Z:Univ.
∀apply:∀_:Univ.∀_:Univ.Univ.
∀b:Univ.
∀f:∀_:Univ.Univ.
∀s:Univ.
∀H0:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (apply (apply (apply b X) Y) Z) (apply X (apply Y Z)).
∀H1:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (apply (apply (apply s X) Y) Z) (apply (apply X Z) (apply Y Z)).∃Y:Univ.eq Univ (apply Y (f Y)) (apply (f Y) (apply Y (f Y))))
.
#Univ ##.
#X ##.
#Y ##.
#Z ##.
#apply ##.
#b ##.
#f ##.
#s ##.
#H0 ##.
#H1 ##.
napply (ex_intro ? ? ? ?) ##[
##2:
nauto by H0,H1 ##;
##| ##skip ##]
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)

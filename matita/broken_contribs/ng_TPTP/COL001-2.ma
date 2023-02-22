include "logic/equality.ma".

(* Inclusion of: COL001-2.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : COL001-2 : TPTP v3.7.0. Released v1.0.0. *)

(*  Domain   : Combinatory Logic *)

(*  Problem  : Weak fixed point for S and K *)

(*  Version  : [WM88] (equality) axioms : Augmented. *)

(*  English  : The weak fixed point property holds for the set P consisting  *)

(*             of the combinators S and K alone, where ((Sx)y)z = (xz)(yz)  *)

(*             and (Kx)y = x. *)

(*  Refs     : [WM88]  Wos & McCune (1988), Challenge Problems Focusing on Eq *)

(*  Source   : [TPTP] *)

(*  Names    :  *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.11 v3.4.0, 0.12 v3.3.0, 0.07 v3.1.0, 0.11 v2.7.0, 0.00 v2.1.0, 0.13 v2.0.0 *)

(*  Syntax   : Number of clauses     :    6 (   0 non-Horn;   6 unit;   1 RR) *)

(*             Number of atoms       :    6 (   6 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    7 (   6 constant; 0-2 arity) *)

(*             Number of variables   :   11 (   1 singleton) *)

(*             Maximal term depth    :    6 (   3 average) *)

(*  Comments : This allows the use of B and I in the proof, as done in the *)

(*             "Proof of Theorem C1" in [WM88]. *)

(* -------------------------------------------------------------------------- *)
ntheorem prove_fixed_point:
 (∀Univ:Type.∀X:Univ.∀Y:Univ.∀Z:Univ.
∀apply:∀_:Univ.∀_:Univ.Univ.
∀b:Univ.
∀combinator:Univ.
∀i:Univ.
∀k:Univ.
∀s:Univ.
∀x:Univ.
∀H0:∀X:Univ.eq Univ (apply (apply (apply s (apply b X)) i) (apply (apply s (apply b X)) i)) (apply x (apply (apply (apply s (apply b X)) i) (apply (apply s (apply b X)) i))).
∀H1:∀X:Univ.eq Univ (apply i X) X.
∀H2:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (apply (apply (apply b X) Y) Z) (apply X (apply Y Z)).
∀H3:∀X:Univ.∀Y:Univ.eq Univ (apply (apply k X) Y) X.
∀H4:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (apply (apply (apply s X) Y) Z) (apply (apply X Z) (apply Y Z)).∃Y:Univ.eq Univ Y (apply combinator Y))
.
#Univ ##.
#X ##.
#Y ##.
#Z ##.
#apply ##.
#b ##.
#combinator ##.
#i ##.
#k ##.
#s ##.
#x ##.
#H0 ##.
#H1 ##.
#H2 ##.
#H3 ##.
#H4 ##.
napply (ex_intro ? ? ? ?) ##[
##2:
nauto by H0,H1,H2,H3,H4 ##;
##| ##skip ##]
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)

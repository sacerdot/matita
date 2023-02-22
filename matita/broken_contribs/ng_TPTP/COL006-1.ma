include "logic/equality.ma".

(* Inclusion of: COL006-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : COL006-1 : TPTP v3.7.0. Released v1.0.0. *)

(*  Domain   : Combinatory Logic *)

(*  Problem  : Strong fixed point for S and K *)

(*  Version  : [WM88] (equality) axioms. *)

(*  English  : The strong fixed point property holds for the set  *)

(*             P consisting of the combinators S and K alone, where  *)

(*             ((Sx)y)z = (xz)(yz), (Kx)y = x. *)

(*  Refs     : [WM88]  Wos & McCune (1988), Challenge Problems Focusing on Eq *)

(*  Source   : [WM88] *)

(*  Names    : Problem 6 [WM88] *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.56 v3.4.0, 0.50 v3.3.0, 0.57 v3.1.0, 0.78 v2.7.0, 0.64 v2.6.0, 0.67 v2.5.0, 0.50 v2.4.0, 0.67 v2.2.1, 0.67 v2.2.0, 0.57 v2.1.0, 1.00 v2.0.0 *)

(*  Syntax   : Number of clauses     :    3 (   0 non-Horn;   3 unit;   1 RR) *)

(*             Number of atoms       :    3 (   3 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    4 (   2 constant; 0-2 arity) *)

(*             Number of variables   :    6 (   1 singleton) *)

(*             Maximal term depth    :    4 (   3 average) *)

(*  Comments :  *)

(* -------------------------------------------------------------------------- *)
ntheorem prove_fixed_point:
 (∀Univ:Type.∀X:Univ.∀Y:Univ.∀Z:Univ.
∀apply:∀_:Univ.∀_:Univ.Univ.
∀f:∀_:Univ.Univ.
∀k:Univ.
∀s:Univ.
∀H0:∀X:Univ.∀Y:Univ.eq Univ (apply (apply k X) Y) X.
∀H1:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (apply (apply (apply s X) Y) Z) (apply (apply X Z) (apply Y Z)).∃Y:Univ.eq Univ (apply Y (f Y)) (apply (f Y) (apply Y (f Y))))
.
#Univ ##.
#X ##.
#Y ##.
#Z ##.
#apply ##.
#f ##.
#k ##.
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

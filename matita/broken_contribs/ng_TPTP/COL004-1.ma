include "logic/equality.ma".

(* Inclusion of: COL004-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : COL004-1 : TPTP v3.7.0. Released v1.0.0. *)

(*  Domain   : Combinatory Logic *)

(*  Problem  : Find combinator equivalent to U from S and K *)

(*  Version  : [WM88] (equality) axioms. *)

(*  English  : Construct from S and K alone a combinator that behaves as the  *)

(*             combinator U does, where ((Sx)y)z = (xz)(yz), (Kx)y  *)

(*             = x, (Ux)y = y((xx)y). *)

(*  Refs     : [WM88]  Wos & McCune (1988), Challenge Problems Focusing on Eq *)

(*  Source   : [WM88] *)

(*  Names    : Problem 4 [WM88] *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.44 v3.4.0, 0.38 v3.3.0, 0.50 v3.2.0, 0.57 v3.1.0, 0.67 v2.7.0, 0.55 v2.6.0, 0.17 v2.5.0, 0.25 v2.4.0, 0.00 v2.2.1, 0.56 v2.2.0, 0.57 v2.1.0, 1.00 v2.0.0 *)

(*  Syntax   : Number of clauses     :    3 (   0 non-Horn;   3 unit;   1 RR) *)

(*             Number of atoms       :    3 (   3 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    5 (   2 constant; 0-2 arity) *)

(*             Number of variables   :    6 (   1 singleton) *)

(*             Maximal term depth    :    5 (   3 average) *)

(*  Comments :  *)

(* -------------------------------------------------------------------------- *)
ntheorem prove_u_combinator:
 (∀Univ:Type.∀X:Univ.∀Y:Univ.∀Z:Univ.
∀apply:∀_:Univ.∀_:Univ.Univ.
∀f:∀_:Univ.Univ.
∀g:∀_:Univ.Univ.
∀k:Univ.
∀s:Univ.
∀H0:∀X:Univ.∀Y:Univ.eq Univ (apply (apply k X) Y) X.
∀H1:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (apply (apply (apply s X) Y) Z) (apply (apply X Z) (apply Y Z)).∃Z:Univ.eq Univ (apply (apply Z (f Z)) (g Z)) (apply (g Z) (apply (apply (f Z) (f Z)) (g Z))))
.
#Univ ##.
#X ##.
#Y ##.
#Z ##.
#apply ##.
#f ##.
#g ##.
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

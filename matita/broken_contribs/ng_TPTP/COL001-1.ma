include "logic/equality.ma".

(* Inclusion of: COL001-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : COL001-1 : TPTP v3.7.0. Released v1.0.0. *)

(*  Domain   : Combinatory Logic *)

(*  Problem  : Weak fixed point for S and K *)

(*  Version  : [WM88] (equality) axioms. *)

(*  English  : The weak fixed point property holds for the set P consisting  *)

(*             of the combinators S and K alone, where ((Sx)y)z = (xz)(yz)  *)

(*             and (Kx)y = x. *)

(*  Refs     : [Smu85] Smullyan (1978), To Mock a Mocking Bird and Other Logi *)

(*           : [WM88]  Wos & McCune (1988), Challenge Problems Focusing on Eq *)

(*  Source   : [WM88] *)

(*  Names    : C1 [WM88] *)

(*           : Problem 1 [WM88] *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.11 v3.4.0, 0.12 v3.3.0, 0.07 v3.1.0, 0.11 v2.7.0, 0.00 v2.1.0, 0.13 v2.0.0 *)

(*  Syntax   : Number of clauses     :    3 (   0 non-Horn;   3 unit;   1 RR) *)

(*             Number of atoms       :    3 (   3 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    4 (   3 constant; 0-2 arity) *)

(*             Number of variables   :    6 (   1 singleton) *)

(*             Maximal term depth    :    4 (   2 average) *)

(*  Comments :  *)

(* -------------------------------------------------------------------------- *)
ntheorem prove_fixed_point:
 (∀Univ:Type.∀X:Univ.∀Y:Univ.∀Z:Univ.
∀apply:∀_:Univ.∀_:Univ.Univ.
∀combinator:Univ.
∀k:Univ.
∀s:Univ.
∀H0:∀X:Univ.∀Y:Univ.eq Univ (apply (apply k X) Y) X.
∀H1:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (apply (apply (apply s X) Y) Z) (apply (apply X Z) (apply Y Z)).∃Y:Univ.eq Univ Y (apply combinator Y))
.
#Univ ##.
#X ##.
#Y ##.
#Z ##.
#apply ##.
#combinator ##.
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

include "logic/equality.ma".

(* Inclusion of: COL071-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : COL071-1 : TPTP v3.7.0. Released v1.2.0. *)

(*  Domain   : Combinatory Logic *)

(*  Problem  : Strong fixed point for N and Q *)

(*  Version  : [WM88] (equality) axioms. *)

(*  English  : The strong fixed point property holds for the set  *)

(*             P consisting of the combinators N and Q, where ((Nx)y)z  *)

(*             = ((xz)y)z, ((Qx)y)z = y(xz). *)

(*  Refs     : [WM88]  Wos & McCune (1988), Challenge Problems Focusing on Eq *)

(*           : [Wos93] Wos (1993), The Kernel Strategy and Its Use for the St *)

(*           : [Zha95] Zhang (1995), Email to G. Sutcliffe *)

(*  Source   : [Wos93] *)

(*  Names    : Question 14 [Wos93] *)

(*  Status   : Satisfiable *)

(*  Rating   : 0.33 v3.2.0, 0.67 v3.1.0, 0.33 v2.4.0, 1.00 v2.3.0, 0.67 v2.2.1, 0.75 v2.2.0, 1.00 v2.0.0 *)

(*  Syntax   : Number of clauses     :    3 (   0 non-Horn;   3 unit;   1 RR) *)

(*             Number of atoms       :    3 (   3 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    4 (   2 constant; 0-2 arity) *)

(*             Number of variables   :    7 (   0 singleton) *)

(*             Maximal term depth    :    4 (   4 average) *)

(*  Comments : [Zha95] provided a 4 element model of these clauses. *)

(* -------------------------------------------------------------------------- *)
ntheorem prove_fixed_point:
 (∀Univ:Type.∀X:Univ.∀Y:Univ.∀Z:Univ.
∀apply:∀_:Univ.∀_:Univ.Univ.
∀f:∀_:Univ.Univ.
∀n:Univ.
∀q:Univ.
∀H0:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (apply (apply (apply q X) Y) Z) (apply Y (apply X Z)).
∀H1:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (apply (apply (apply n X) Y) Z) (apply (apply (apply X Z) Y) Z).∃Y:Univ.eq Univ (apply Y (f Y)) (apply (f Y) (apply Y (f Y))))
.
#Univ ##.
#X ##.
#Y ##.
#Z ##.
#apply ##.
#f ##.
#n ##.
#q ##.
#H0 ##.
#H1 ##.
napply (ex_intro ? ? ? ?) ##[
##2:
nauto by H0,H1 ##;
##| ##skip ##]
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)

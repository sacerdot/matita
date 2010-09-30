include "logic/equality.ma".

(* Inclusion of: COL002-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : COL002-1 : TPTP v3.7.0. Released v1.0.0. *)

(*  Domain   : Combinatory Logic *)

(*  Problem  : Weak fixed point for S, B, C, and I *)

(*  Version  : [WM88] (equality) axioms. *)

(*  English  : The weak fixed point property holds for the set P consisting  *)

(*             of the combinators S, B, C, and I, where ((Sx)y)z = (xz)(yz),  *)

(*             ((Bx)y)z = x(yz), ((Cx)y)z = (xz)y, and Ix = x. *)

(*  Refs     : [WM88]  Wos & McCune (1988), Challenge Problems Focusing on Eq *)

(*  Source   : [WM88] *)

(*  Names    : C1.1 [WM88] *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.11 v3.4.0, 0.12 v3.3.0, 0.00 v2.1.0, 0.13 v2.0.0 *)

(*  Syntax   : Number of clauses     :    5 (   0 non-Horn;   5 unit;   1 RR) *)

(*             Number of atoms       :    5 (   5 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    6 (   5 constant; 0-2 arity) *)

(*             Number of variables   :   11 (   0 singleton) *)

(*             Maximal term depth    :    4 (   3 average) *)

(*  Comments :  *)

(* -------------------------------------------------------------------------- *)
ntheorem prove_fixed_point:
 (∀Univ:Type.∀X:Univ.∀Y:Univ.∀Z:Univ.
∀apply:∀_:Univ.∀_:Univ.Univ.
∀b:Univ.
∀c:Univ.
∀fixed_pt:Univ.
∀i:Univ.
∀s:Univ.
∀H0:∀X:Univ.eq Univ (apply i X) X.
∀H1:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (apply (apply (apply c X) Y) Z) (apply (apply X Z) Y).
∀H2:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (apply (apply (apply b X) Y) Z) (apply X (apply Y Z)).
∀H3:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (apply (apply (apply s X) Y) Z) (apply (apply X Z) (apply Y Z)).∃Y:Univ.eq Univ Y (apply fixed_pt Y))
.
#Univ ##.
#X ##.
#Y ##.
#Z ##.
#apply ##.
#b ##.
#c ##.
#fixed_pt ##.
#i ##.
#s ##.
#H0 ##.
#H1 ##.
#H2 ##.
#H3 ##.
napply (ex_intro ? ? ? ?) ##[
##2:
nauto by H0,H1,H2,H3 ##;
##| ##skip ##]
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)

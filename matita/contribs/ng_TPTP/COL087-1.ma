include "logic/equality.ma".

(* Inclusion of: COL087-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : COL087-1 : TPTP v3.7.0. Released v2.7.0. *)

(*  Domain   : Combinatory Logic *)

(*  Problem  : Strong fixed point for B and M *)

(*  Version  : [Cla03] axioms. *)

(*  English  : The strong fixed point property holds for the set with the *)

(*             combinators B and M as a basis, where Bxyz = x(yz) and *)

(*             Mx = xx. *)

(*  Refs     : [WM88]  Wos & McCune (1988), Challenge Problems Focusing on Eq *)

(*           : [Cla03] Claessen (2003), Email to G. Sutcliffe *)

(*  Source   : [Cla03] *)

(*  Names    : *)

(*  Status   : Open *)

(*  Rating   : 1.00 v2.7.0 *)

(*  Syntax   : Number of clauses     :    3 (   0 non-Horn;   3 unit;   1 RR) *)

(*             Number of atoms       :    3 (   3 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    4 (   2 constant; 0-2 arity) *)

(*             Number of variables   :    5 (   0 singleton) *)

(*             Maximal term depth    :    4 (   3 average) *)

(*  Comments :  *)

(* -------------------------------------------------------------------------- *)
ntheorem strong_fixpoint:
 (∀Univ:Type.∀X:Univ.∀Y:Univ.∀Z:Univ.
∀apply:∀_:Univ.∀_:Univ.Univ.
∀b:Univ.
∀f:∀_:Univ.Univ.
∀m:Univ.
∀H0:∀X:Univ.eq Univ (apply m X) (apply X X).
∀H1:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (apply (apply (apply b X) Y) Z) (apply X (apply Y Z)).∃Y:Univ.eq Univ (apply Y (f Y)) (apply (f Y) (apply Y (f Y))))
.
#Univ ##.
#X ##.
#Y ##.
#Z ##.
#apply ##.
#b ##.
#f ##.
#m ##.
#H0 ##.
#H1 ##.
napply (ex_intro ? ? ? ?) ##[
##2:
nauto by H0,H1 ##;
##| ##skip ##]
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)

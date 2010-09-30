include "logic/equality.ma".

(* Inclusion of: SYN083-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : SYN083-1 : TPTP v3.7.0. Released v1.0.0. *)

(*  Domain   : Syntactic *)

(*  Problem  : Pelletier Problem 61 *)

(*  Version  : Especial. *)

(*  English  :  *)

(*  Refs     : [Pel86] Pelletier (1986), Seventy-five Problems for Testing Au *)

(*  Source   : [Pel86] *)

(*  Names    : Pelletier 61 [Pel86] *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.00 v2.0.0 *)

(*  Syntax   : Number of clauses     :    2 (   0 non-Horn;   2 unit;   1 RR) *)

(*             Number of atoms       :    2 (   2 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    5 (   4 constant; 0-2 arity) *)

(*             Number of variables   :    3 (   0 singleton) *)

(*             Maximal term depth    :    4 (   4 average) *)

(*  Comments :  *)

(* -------------------------------------------------------------------------- *)
ntheorem prove_this:
 (∀Univ:Type.∀X:Univ.∀Y:Univ.∀Z:Univ.
∀a:Univ.
∀b:Univ.
∀c:Univ.
∀d:Univ.
∀f:∀_:Univ.∀_:Univ.Univ.
∀H0:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (f X (f Y Z)) (f (f X Y) Z).eq Univ (f a (f b (f c d))) (f (f (f a b) c) d))
.
#Univ ##.
#X ##.
#Y ##.
#Z ##.
#a ##.
#b ##.
#c ##.
#d ##.
#f ##.
#H0 ##.
nauto by H0 ##;
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)

include "logic/equality.ma".

(* Inclusion of: SYN080-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : SYN080-1 : TPTP v3.7.0. Released v1.0.0. *)

(*  Domain   : Syntactic *)

(*  Problem  : Pelletier Problem 58 *)

(*  Version  : Especial. *)

(*  English  :  *)

(*  Refs     : [Pel86] Pelletier (1986), Seventy-five Problems for Testing Au *)

(*  Source   : [Pel86] *)

(*  Names    : Pelletier 58 [Pel86] *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.00 v3.4.0, 0.12 v3.3.0, 0.00 v2.0.0 *)

(*  Syntax   : Number of clauses     :    2 (   0 non-Horn;   2 unit;   1 RR) *)

(*             Number of atoms       :    2 (   2 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    4 (   2 constant; 0-1 arity) *)

(*             Number of variables   :    2 (   2 singleton) *)

(*             Maximal term depth    :    3 (   2 average) *)

(*  Comments :  *)

(* -------------------------------------------------------------------------- *)
ntheorem prove_this:
 (∀Univ:Type.∀X:Univ.∀Y:Univ.
∀a:Univ.
∀b:Univ.
∀f:∀_:Univ.Univ.
∀g:∀_:Univ.Univ.
∀H0:∀X:Univ.∀Y:Univ.eq Univ (f X) (g Y).eq Univ (f (f a)) (f (g b)))
.
#Univ ##.
#X ##.
#Y ##.
#a ##.
#b ##.
#f ##.
#g ##.
#H0 ##.
nauto by H0 ##;
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)

include "logic/equality.ma".

(* Inclusion of: GRP118-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : GRP118-1 : TPTP v3.7.0. Released v1.2.0. *)

(*  Domain   : Group Theory *)

(*  Problem  : Derive associativity from a single axiom for groups order 3 *)

(*  Version  : [Wos96] (equality) axioms. *)

(*  English  :  *)

(*  Refs     : [Wos96] Wos (1996), The Automation of Reasoning: An Experiment  *)

(*  Source   : [OTTER] *)

(*  Names    : groups.exp3.in part 4 [OTTER] *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.11 v3.4.0, 0.00 v2.2.1, 0.22 v2.2.0, 0.29 v2.1.0, 0.14 v2.0.0 *)

(*  Syntax   : Number of clauses     :    2 (   0 non-Horn;   2 unit;   1 RR) *)

(*             Number of atoms       :    2 (   2 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    5 (   4 constant; 0-2 arity) *)

(*             Number of variables   :    3 (   0 singleton) *)

(*             Maximal term depth    :    6 (   3 average) *)

(*  Comments :  *)

(* -------------------------------------------------------------------------- *)
ntheorem prove_order3:
 (∀Univ:Type.∀X:Univ.∀Y:Univ.∀Z:Univ.
∀a:Univ.
∀b:Univ.
∀c:Univ.
∀identity:Univ.
∀multiply:∀_:Univ.∀_:Univ.Univ.
∀H0:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (multiply X (multiply (multiply X (multiply (multiply X Y) Z)) (multiply identity (multiply Z Z)))) Y.eq Univ (multiply (multiply a b) c) (multiply a (multiply b c)))
.
#Univ ##.
#X ##.
#Y ##.
#Z ##.
#a ##.
#b ##.
#c ##.
#identity ##.
#multiply ##.
#H0 ##.
nauto by H0 ##;
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)

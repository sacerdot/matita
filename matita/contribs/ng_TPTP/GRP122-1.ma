include "logic/equality.ma".

(* Inclusion of: GRP122-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : GRP122-1 : TPTP v3.7.0. Released v1.2.0. *)

(*  Domain   : Group Theory *)

(*  Problem  : Derive associativity from a single axiom for groups order 4 *)

(*  Version  : [Wos96] (equality) axioms. *)

(*  English  :  *)

(*  Refs     : [Wos96] Wos (1996), The Automation of Reasoning: An Experiment  *)

(*  Source   : [OTTER] *)

(*  Names    : groups.exp4.in part 4 [OTTER] *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.11 v3.4.0, 0.12 v3.3.0, 0.14 v3.2.0, 0.07 v3.1.0, 0.22 v2.7.0, 0.00 v2.2.1, 0.56 v2.2.0, 0.57 v2.1.0, 0.43 v2.0.0 *)

(*  Syntax   : Number of clauses     :    3 (   0 non-Horn;   3 unit;   2 RR) *)

(*             Number of atoms       :    3 (   3 equality) *)

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
∀H0:eq Univ (multiply identity identity) identity.
∀H1:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (multiply Y (multiply (multiply Y (multiply (multiply Y Y) (multiply X Z))) (multiply Z (multiply Z Z)))) X.eq Univ (multiply (multiply a b) c) (multiply a (multiply b c)))
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
#H1 ##.
nauto by H0,H1 ##;
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)

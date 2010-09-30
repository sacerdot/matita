include "logic/equality.ma".

(* Inclusion of: GRP119-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : GRP119-1 : TPTP v3.7.0. Bugfixed v1.2.1. *)

(*  Domain   : Group Theory *)

(*  Problem  : Derive order 4 from a single axiom for groups order 4 *)

(*  Version  : [Wos96] (equality) axioms. *)

(*  English  :  *)

(*  Refs     : [Wos96] Wos (1996), The Automation of Reasoning: An Experiment  *)

(*  Source   : [OTTER] *)

(*  Names    : groups.exp4.in part 1 [OTTER] *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.11 v3.4.0, 0.12 v3.3.0, 0.00 v3.1.0, 0.11 v2.7.0, 0.00 v2.2.1, 0.44 v2.2.0, 0.57 v2.1.0, 0.29 v2.0.0 *)

(*  Syntax   : Number of clauses     :    3 (   0 non-Horn;   3 unit;   2 RR) *)

(*             Number of atoms       :    3 (   3 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    3 (   2 constant; 0-2 arity) *)

(*             Number of variables   :    3 (   0 singleton) *)

(*             Maximal term depth    :    6 (   2 average) *)

(*  Comments :  *)

(*  Bugfixes : v1.2.1 - Clause prove_order4 fixed. *)

(* -------------------------------------------------------------------------- *)
ntheorem prove_order4:
 (∀Univ:Type.∀X:Univ.∀Y:Univ.∀Z:Univ.
∀a:Univ.
∀identity:Univ.
∀multiply:∀_:Univ.∀_:Univ.Univ.
∀H0:eq Univ (multiply identity identity) identity.
∀H1:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (multiply Y (multiply (multiply Y (multiply (multiply Y Y) (multiply X Z))) (multiply Z (multiply Z Z)))) X.eq Univ (multiply a (multiply a (multiply a a))) identity)
.
#Univ ##.
#X ##.
#Y ##.
#Z ##.
#a ##.
#identity ##.
#multiply ##.
#H0 ##.
#H1 ##.
nauto by H0,H1 ##;
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)

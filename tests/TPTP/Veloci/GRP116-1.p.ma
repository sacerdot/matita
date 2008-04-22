
include "logic/equality.ma".
(* Inclusion of: GRP116-1.p *)
(* -------------------------------------------------------------------------- *)
(*  File     : GRP116-1 : TPTP v3.1.1. Released v1.2.0. *)
(*  Domain   : Group Theory *)
(*  Problem  : Derive left identity from a single axiom for groups order 3 *)
(*  Version  : [Wos96] (equality) axioms. *)
(*  English  :  *)
(*  Refs     : [Wos96] Wos (1996), The Automation of Reasoning: An Experiment  *)
(*  Source   : [OTTER] *)
(*  Names    : groups.exp3.in part 2 [OTTER] *)
(*  Status   : Unsatisfiable *)
(*  Rating   : 0.00 v2.2.1, 0.22 v2.2.0, 0.29 v2.1.0, 0.14 v2.0.0 *)
(*  Syntax   : Number of clauses     :    2 (   0 non-Horn;   2 unit;   1 RR) *)
(*             Number of atoms       :    2 (   2 equality) *)
(*             Maximal clause size   :    1 (   1 average) *)
(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)
(*             Number of functors    :    3 (   2 constant; 0-2 arity) *)
(*             Number of variables   :    3 (   0 singleton) *)
(*             Maximal term depth    :    6 (   2 average) *)
(*  Comments :  *)
(* -------------------------------------------------------------------------- *)
theorem prove_order3:
 \forall Univ:Set.
\forall a:Univ.
\forall identity:Univ.
\forall multiply:\forall _:Univ.\forall _:Univ.Univ.
\forall H0:\forall X:Univ.\forall Y:Univ.\forall Z:Univ.eq Univ (multiply X (multiply (multiply X (multiply (multiply X Y) Z)) (multiply identity (multiply Z Z)))) Y.eq Univ (multiply identity a) a
.
intros.
autobatch paramodulation timeout=100;
try assumption.
print proofterm.
qed.
(* -------------------------------------------------------------------------- *)

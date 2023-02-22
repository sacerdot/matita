
include "logic/equality.ma".
(* Inclusion of: COL008-1.p *)
(* -------------------------------------------------------------------------- *)
(*  File     : COL008-1 : TPTP v3.1.1. Released v1.0.0. *)
(*  Domain   : Combinatory Logic *)
(*  Problem  : Weak fixed point for M and B *)
(*  Version  : [WM88] (equality) axioms. *)
(*  English  : The weak fixed point property holds for the set P consisting  *)
(*             of the combinators M and B, where ((Bx)y)z = x(yz), Mx = xx. *)
(*  Refs     : [Smu85] Smullyan (1978), To Mock a Mocking Bird and Other Logi *)
(*           : [MW87]  McCune & Wos (1987), A Case Study in Automated Theorem *)
(*           : [WM88]  Wos & McCune (1988), Challenge Problems Focusing on Eq *)
(*           : [MW88]  McCune & Wos (1988), Some Fixed Point Problems in Comb *)
(*           : [Wos93] Wos (1993), The Kernel Strategy and Its Use for the St *)
(*  Source   : [MW88] *)
(*  Names    : - [MW88] *)
(*           : Question 13 [Wos93] *)
(*  Status   : Unsatisfiable *)
(*  Rating   : 0.00 v2.0.0 *)
(*  Syntax   : Number of clauses     :    3 (   0 non-Horn;   3 unit;   1 RR) *)
(*             Number of atoms       :    3 (   3 equality) *)
(*             Maximal clause size   :    1 (   1 average) *)
(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)
(*             Number of functors    :    4 (   3 constant; 0-2 arity) *)
(*             Number of variables   :    5 (   0 singleton) *)
(*             Maximal term depth    :    4 (   2 average) *)
(*  Comments :  *)
(* -------------------------------------------------------------------------- *)
theorem prove_fixed_point:
 \forall Univ:Set.
\forall apply:\forall _:Univ.\forall _:Univ.Univ.
\forall b:Univ.
\forall combinator:Univ.
\forall m:Univ.
\forall H0:\forall X:Univ.eq Univ (apply m X) (apply X X).
\forall H1:\forall X:Univ.\forall Y:Univ.\forall Z:Univ.eq Univ (apply (apply (apply b X) Y) Z) (apply X (apply Y Z)).\exist Y:Univ.eq Univ Y (apply combinator Y)
.
intros.
exists[
2:
autobatch paramodulation timeout=100;
try assumption.
|
skip]
print proofterm.
qed.
(* -------------------------------------------------------------------------- *)

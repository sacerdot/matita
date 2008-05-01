
include "logic/equality.ma".
(* Inclusion of: COL007-1.p *)
(* -------------------------------------------------------------------------- *)
(*  File     : COL007-1 : TPTP v3.1.1. Released v1.0.0. *)
(*  Domain   : Combinatory Logic *)
(*  Problem  : Weak fixed point for L *)
(*  Version  : [WM88] (equality) axioms. *)
(*  English  : The weak fixed point property holds for the set P consisting  *)
(*             of the combinator L, where (Lx)y = x(yy). *)
(*  Refs     : [Smu85] Smullyan (1978), To Mock a Mocking Bird and Other Logi *)
(*           : [MW87]  McCune & Wos (1987), A Case Study in Automated Theorem *)
(*           : [WM88]  Wos & McCune (1988), Challenge Problems Focusing on Eq *)
(*           : [MW88]  McCune & Wos (1988), Some Fixed Point Problems in Comb *)
(*  Source   : [MW88] *)
(*  Names    : - [MW88] *)
(*  Status   : Unsatisfiable *)
(*  Rating   : 0.00 v2.0.0 *)
(*  Syntax   : Number of clauses     :    2 (   0 non-Horn;   2 unit;   1 RR) *)
(*             Number of atoms       :    2 (   2 equality) *)
(*             Maximal clause size   :    1 (   1 average) *)
(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)
(*             Number of functors    :    3 (   2 constant; 0-2 arity) *)
(*             Number of variables   :    3 (   0 singleton) *)
(*             Maximal term depth    :    3 (   2 average) *)
(*  Comments :  *)
(* -------------------------------------------------------------------------- *)
theorem prove_fixed_point:
 \forall Univ:Set.
\forall apply:\forall _:Univ.\forall _:Univ.Univ.
\forall combinator:Univ.
\forall l:Univ.
\forall H0:\forall X:Univ.\forall Y:Univ.eq Univ (apply (apply l X) Y) (apply X (apply Y Y)).\exist Y:Univ.eq Univ Y (apply combinator Y)
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

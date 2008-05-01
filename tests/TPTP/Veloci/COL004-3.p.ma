
include "logic/equality.ma".
(* Inclusion of: COL004-3.p *)
(* -------------------------------------------------------------------------- *)
(*  File     : COL004-3 : TPTP v3.1.1. Released v1.0.0. *)
(*  Domain   : Combinatory Logic *)
(*  Problem  : Find combinator equivalent to U from S and K. *)
(*  Version  : [WM88] (equality) axioms. *)
(*             Theorem formulation : The combination is provided and checked. *)
(*  English  : Construct from S and K alone a combinator that behaves as the  *)
(*             combinator U does, where ((Sx)y)z = (xz)(yz), (Kx)y = x,  *)
(*             (Ux)y = y((xx)y). *)
(*  Refs     : [WM88]  Wos & McCune (1988), Challenge Problems Focusing on Eq *)
(*  Source   : [TPTP] *)
(*  Names    :  *)
(*  Status   : Unsatisfiable *)
(*  Rating   : 0.21 v3.1.0, 0.22 v2.7.0, 0.27 v2.6.0, 0.17 v2.5.0, 0.00 v2.2.1, 0.22 v2.2.0, 0.29 v2.1.0, 0.38 v2.0.0 *)
(*  Syntax   : Number of clauses     :    3 (   0 non-Horn;   3 unit;   1 RR) *)
(*             Number of atoms       :    3 (   3 equality) *)
(*             Maximal clause size   :    1 (   1 average) *)
(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)
(*             Number of functors    :    5 (   4 constant; 0-2 arity) *)
(*             Number of variables   :    5 (   1 singleton) *)
(*             Maximal term depth    :    9 (   4 average) *)
(*  Comments :  *)
(* -------------------------------------------------------------------------- *)
(* ----This is the U equivalent *)
theorem prove_u_combinator:
 \forall Univ:Set.
\forall apply:\forall _:Univ.\forall _:Univ.Univ.
\forall k:Univ.
\forall s:Univ.
\forall x:Univ.
\forall y:Univ.
\forall H0:\forall X:Univ.\forall Y:Univ.eq Univ (apply (apply k X) Y) X.
\forall H1:\forall X:Univ.\forall Y:Univ.\forall Z:Univ.eq Univ (apply (apply (apply s X) Y) Z) (apply (apply X Z) (apply Y Z)).eq Univ (apply (apply (apply (apply s (apply k (apply s (apply (apply s k) k)))) (apply (apply s (apply (apply s k) k)) (apply (apply s k) k))) x) y) (apply y (apply (apply x x) y))
.
intros.
autobatch paramodulation timeout=100;
try assumption.
print proofterm.
qed.
(* -------------------------------------------------------------------------- *)

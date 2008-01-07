
include "logic/equality.ma".
(* Inclusion of: COL060-2.p *)
(* -------------------------------------------------------------------------- *)
(*  File     : COL060-2 : TPTP v3.1.1. Bugfixed v1.2.0. *)
(*  Domain   : Combinatory Logic *)
(*  Problem  : Find combinator equivalent to Q from B and T *)
(*  Version  : [WM88] (equality) axioms. *)
(*             Theorem formulation : The combinator is provided and checked. *)
(*  English  : Construct from B and T alone a combinator that behaves as the  *)
(*             combinator Q does, where ((Bx)y)z = x(yz), (Tx)y = yx,  *)
(*             ((Qx)y)z = y(xz). *)
(*  Refs     : [WM88]  Wos & McCune (1988), Challenge Problems Focusing on Eq *)
(*           : [WW+90] Wos et al. (1990), Automated Reasoning Contributes to  *)
(*  Source   : [TPTP] *)
(*  Names    :  *)
(*  Status   : Unsatisfiable *)
(*  Rating   : 0.00 v2.1.0, 0.29 v2.0.0 *)
(*  Syntax   : Number of clauses     :    3 (   0 non-Horn;   3 unit;   1 RR) *)
(*             Number of atoms       :    3 (   3 equality) *)
(*             Maximal clause size   :    1 (   1 average) *)
(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)
(*             Number of functors    :    6 (   5 constant; 0-2 arity) *)
(*             Number of variables   :    5 (   0 singleton) *)
(*             Maximal term depth    :    7 (   4 average) *)
(*  Comments :  *)
(*  Bugfixes : v1.2.0 : Redundant [fgh]_substitution axioms removed. *)
(* -------------------------------------------------------------------------- *)
(* ----This is the q equivalent *)
theorem prove_q_combinator:
 \forall Univ:Set.
\forall apply:\forall _:Univ.\forall _:Univ.Univ.
\forall b:Univ.
\forall t:Univ.
\forall x:Univ.
\forall y:Univ.
\forall z:Univ.
\forall H0:\forall X:Univ.\forall Y:Univ.eq Univ (apply (apply t X) Y) (apply Y X).
\forall H1:\forall X:Univ.\forall Y:Univ.\forall Z:Univ.eq Univ (apply (apply (apply b X) Y) Z) (apply X (apply Y Z)).eq Univ (apply (apply (apply (apply (apply b (apply t b)) (apply (apply b b) t)) x) y) z) (apply y (apply x z))
.
intros.
autobatch paramodulation timeout=100;
try assumption.
print proofterm.
qed.
(* -------------------------------------------------------------------------- *)


include "logic/equality.ma".
(* Inclusion of: LDA001-1.p *)
(* -------------------------------------------------------------------------- *)
(*  File     : LDA001-1 : TPTP v3.1.1. Released v1.0.0. *)
(*  Domain   : LD-Algebras *)
(*  Problem  : Verify 3*2*U = UUU, where U = 2*2 *)
(*  Version  : [Jec93] (equality) axioms. *)
(*  English  :  *)
(*  Refs     : [Jec93] Jech (1993), LD-Algebras *)
(*  Source   : [Jec93] *)
(*  Names    : Problem 1 [Jec93] *)
(*  Status   : Unsatisfiable *)
(*  Rating   : 0.00 v2.2.1, 0.22 v2.2.0, 0.29 v2.1.0, 0.25 v2.0.0 *)
(*  Syntax   : Number of clauses     :    5 (   0 non-Horn;   5 unit;   4 RR) *)
(*             Number of atoms       :    5 (   5 equality) *)
(*             Maximal clause size   :    1 (   1 average) *)
(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)
(*             Number of functors    :    5 (   4 constant; 0-2 arity) *)
(*             Number of variables   :    3 (   0 singleton) *)
(*             Maximal term depth    :    3 (   2 average) *)
(*  Comments :  *)
(* -------------------------------------------------------------------------- *)
(* ----A1: x(yz)=xy(xz)  *)
(* ----3*2*U = U*U*U  *)
theorem prove_equation:
 \forall Univ:Set.
\forall f:\forall _:Univ.\forall _:Univ.Univ.
\forall n1:Univ.
\forall n2:Univ.
\forall n3:Univ.
\forall u:Univ.
\forall H0:eq Univ u (f n2 n2).
\forall H1:eq Univ n3 (f n2 n1).
\forall H2:eq Univ n2 (f n1 n1).
\forall H3:\forall X:Univ.\forall Y:Univ.\forall Z:Univ.eq Univ (f X (f Y Z)) (f (f X Y) (f X Z)).eq Univ (f (f n3 n2) u) (f (f u u) u)
.
intros.
autobatch paramodulation timeout=100;
try assumption.
print proofterm.
qed.
(* -------------------------------------------------------------------------- *)

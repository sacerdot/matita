
include "logic/equality.ma".
(* Inclusion of: BOO001-1.p *)
(* -------------------------------------------------------------------------- *)
(*  File     : BOO001-1 : TPTP v3.1.1. Released v1.0.0. *)
(*  Domain   : Boolean Algebra (Ternary) *)
(*  Problem  : In B3 algebra, inverse is an involution *)
(*  Version  : [OTTER] (equality) axioms. *)
(*  English  :  *)
(*  Refs     :  *)
(*  Source   : [OTTER] *)
(*  Names    : tba_gg.in [OTTER] *)
(*  Status   : Unsatisfiable *)
(*  Rating   : 0.00 v2.2.1, 0.11 v2.2.0, 0.14 v2.1.0, 0.25 v2.0.0 *)
(*  Syntax   : Number of clauses     :    6 (   0 non-Horn;   6 unit;   1 RR) *)
(*             Number of atoms       :    6 (   6 equality) *)
(*             Maximal clause size   :    1 (   1 average) *)
(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)
(*             Number of functors    :    3 (   1 constant; 0-3 arity) *)
(*             Number of variables   :   13 (   2 singleton) *)
(*             Maximal term depth    :    3 (   2 average) *)
(*  Comments :  *)
(* -------------------------------------------------------------------------- *)
(* ----Include ternary Boolean algebra axioms  *)
(* Inclusion of: Axioms/BOO001-0.ax *)
(* -------------------------------------------------------------------------- *)
(*  File     : BOO001-0 : TPTP v3.1.1. Released v1.0.0. *)
(*  Domain   : Algebra (Ternary Boolean) *)
(*  Axioms   : Ternary Boolean algebra (equality) axioms *)
(*  Version  : [OTTER] (equality) axioms. *)
(*  English  :  *)
(*  Refs     : [Wos88] Wos (1988), Automated Reasoning - 33 Basic Research Pr *)
(*           : [Win82] Winker (1982), Generation and Verification of Finite M *)
(*  Source   : [OTTER] *)
(*  Names    :  *)
(*  Status   :  *)
(*  Syntax   : Number of clauses    :    5 (   0 non-Horn;   5 unit;   0 RR) *)
(*             Number of literals   :    5 (   5 equality) *)
(*             Maximal clause size  :    1 (   1 average) *)
(*             Number of predicates :    1 (   0 propositional; 2-2 arity) *)
(*             Number of functors   :    2 (   0 constant; 1-3 arity) *)
(*             Number of variables  :   13 (   2 singleton) *)
(*             Maximal term depth   :    3 (   2 average) *)
(*  Comments : These axioms appear in [Win82], in which ternary_multiply_1 is *)
(*             shown to be independant. *)
(*           : These axioms are also used in [Wos88], p.222. *)
(* -------------------------------------------------------------------------- *)
(* -------------------------------------------------------------------------- *)
(* -------------------------------------------------------------------------- *)
theorem prove_inverse_is_self_cancelling:
 \forall Univ:Set.
\forall a:Univ.
\forall inverse:\forall _:Univ.Univ.
\forall multiply:\forall _:Univ.\forall _:Univ.\forall _:Univ.Univ.
\forall H0:\forall X:Univ.\forall Y:Univ.eq Univ (multiply X Y (inverse Y)) X.
\forall H1:\forall X:Univ.\forall Y:Univ.eq Univ (multiply (inverse Y) Y X) X.
\forall H2:\forall X:Univ.\forall Y:Univ.eq Univ (multiply X X Y) X.
\forall H3:\forall X:Univ.\forall Y:Univ.eq Univ (multiply Y X X) X.
\forall H4:\forall V:Univ.\forall W:Univ.\forall X:Univ.\forall Y:Univ.\forall Z:Univ.eq Univ (multiply (multiply V W X) Y (multiply V W Z)) (multiply V W (multiply X Y Z)).eq Univ (inverse (inverse a)) a
.
intros.
autobatch paramodulation timeout=100;
try assumption.
print proofterm.
qed.
(* -------------------------------------------------------------------------- *)

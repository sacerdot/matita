
include "logic/equality.ma".
(* Inclusion of: ROB009-1.p *)
(* -------------------------------------------------------------------------- *)
(*  File     : ROB009-1 : TPTP v3.1.1. Released v1.0.0. *)
(*  Domain   : Robbins Algebra *)
(*  Problem  : If -(a + -(b + c)) = -(b + -(a + c)) then a = b *)
(*  Version  : [Win90] (equality) axioms. *)
(*  English  :  *)
(*  Refs     : [Win90] Winker (1990), Robbins Algebra: Conditions that make a *)
(*  Source   : [Win90] *)
(*  Names    : Lemma 3.2 [Win90] *)
(*  Status   : Unsatisfiable *)
(*  Rating   : 0.00 v2.2.1, 0.22 v2.2.0, 0.14 v2.1.0, 0.50 v2.0.0 *)
(*  Syntax   : Number of clauses     :    5 (   0 non-Horn;   5 unit;   2 RR) *)
(*             Number of atoms       :    5 (   5 equality) *)
(*             Maximal clause size   :    1 (   1 average) *)
(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)
(*             Number of functors    :    5 (   3 constant; 0-2 arity) *)
(*             Number of variables   :    7 (   0 singleton) *)
(*             Maximal term depth    :    6 (   3 average) *)
(*  Comments :  *)
(* -------------------------------------------------------------------------- *)
(* ----Include axioms for Robbins algebra  *)
(* Inclusion of: Axioms/ROB001-0.ax *)
(* -------------------------------------------------------------------------- *)
(*  File     : ROB001-0 : TPTP v3.1.1. Released v1.0.0. *)
(*  Domain   : Robbins algebra *)
(*  Axioms   : Robbins algebra axioms *)
(*  Version  : [Win90] (equality) axioms. *)
(*  English  :  *)
(*  Refs     : [HMT71] Henkin et al. (1971), Cylindrical Algebras *)
(*           : [Win90] Winker (1990), Robbins Algebra: Conditions that make a *)
(*  Source   : [OTTER] *)
(*  Names    : Lemma 2.2 [Win90] *)
(*  Status   :  *)
(*  Syntax   : Number of clauses    :    3 (   0 non-Horn;   3 unit;   0 RR) *)
(*             Number of literals   :    3 (   3 equality) *)
(*             Maximal clause size  :    1 (   1 average) *)
(*             Number of predicates :    1 (   0 propositional; 2-2 arity) *)
(*             Number of functors   :    2 (   0 constant; 1-2 arity) *)
(*             Number of variables  :    7 (   0 singleton) *)
(*             Maximal term depth   :    6 (   3 average) *)
(*  Comments :  *)
(* -------------------------------------------------------------------------- *)
(* -------------------------------------------------------------------------- *)
(* -------------------------------------------------------------------------- *)
theorem prove_result:
 \forall Univ:Set.
\forall a:Univ.
\forall add:\forall _:Univ.\forall _:Univ.Univ.
\forall b:Univ.
\forall c:Univ.
\forall negate:\forall _:Univ.Univ.
\forall H0:eq Univ (negate (add a (negate (add b c)))) (negate (add b (negate (add a c)))).
\forall H1:\forall X:Univ.\forall Y:Univ.eq Univ (negate (add (negate (add X Y)) (negate (add X (negate Y))))) X.
\forall H2:\forall X:Univ.\forall Y:Univ.\forall Z:Univ.eq Univ (add (add X Y) Z) (add X (add Y Z)).
\forall H3:\forall X:Univ.\forall Y:Univ.eq Univ (add X Y) (add Y X).eq Univ a b
.
intros.
autobatch paramodulation timeout=100;
try assumption.
print proofterm.
qed.
(* -------------------------------------------------------------------------- *)

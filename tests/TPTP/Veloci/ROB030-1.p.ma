
include "logic/equality.ma".
(* Inclusion of: ROB030-1.p *)
(* ------------------------------------------------------------------------------ *)
(*  File     : ROB030-1 : TPTP v3.1.1. Released v3.1.0. *)
(*  Domain   : Robbins Algebra *)
(*  Problem  : Exists absorbed element => Exists absorbed within negation element *)
(*  Version  : [Win90] (equality) axioms. *)
(*             Theorem formulation : Denies Huntington's axiom. *)
(*  English  : If there are elements c and d such that c+d=d, then the  *)
(*             algebra is Boolean. *)
(*  Refs     : [Win90] Winker (1990), Robbins Algebra: Conditions that make a *)
(*           : [Loe04] Loechner (2004), Email to Geoff Sutcliffe *)
(*  Source   : [Loe04] *)
(*  Names    : (1) [Loe04] *)
(*  Status   : Unsatisfiable *)
(*  Rating   : 0.00 v3.1.0 *)
(*  Syntax   : Number of clauses     :    5 (   0 non-Horn;   5 unit;   2 RR) *)
(*             Number of atoms       :    5 (   5 equality) *)
(*             Maximal clause size   :    1 (   1 average) *)
(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)
(*             Number of functors    :    4 (   2 constant; 0-2 arity) *)
(*             Number of variables   :    9 (   1 singleton) *)
(*             Maximal term depth    :    6 (   2 average) *)
(*  Comments :  *)
(* ------------------------------------------------------------------------------ *)
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
(* ------------------------------------------------------------------------------ *)
theorem prove_absorption_within_negation:
 \forall Univ:Set.
\forall add:\forall _:Univ.\forall _:Univ.Univ.
\forall c:Univ.
\forall d:Univ.
\forall negate:\forall _:Univ.Univ.
\forall H0:eq Univ (add c d) d.
\forall H1:\forall X:Univ.\forall Y:Univ.eq Univ (negate (add (negate (add X Y)) (negate (add X (negate Y))))) X.
\forall H2:\forall X:Univ.\forall Y:Univ.\forall Z:Univ.eq Univ (add (add X Y) Z) (add X (add Y Z)).
\forall H3:\forall X:Univ.\forall Y:Univ.eq Univ (add X Y) (add Y X).\exist A:Univ.\exist B:Univ.eq Univ (negate (add A B)) (negate B)
.
intros.
exists[
2:
exists[
2:
autobatch paramodulation timeout=100;
try assumption.
|
skip]
|
skip]
print proofterm.
qed.
(* ------------------------------------------------------------------------------ *)

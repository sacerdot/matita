
include "logic/equality.ma".
(* Inclusion of: BOO004-2.p *)
(* -------------------------------------------------------------------------- *)
(*  File     : BOO004-2 : TPTP v3.1.1. Released v1.0.0. *)
(*  Domain   : Boolean Algebra *)
(*  Problem  : Addition is idempotent (X + X = X) *)
(*  Version  : [ANL] (equality) axioms. *)
(*  English  :  *)
(*  Refs     :  *)
(*  Source   : [ANL] *)
(*  Names    : prob2_part2.ver2.in [ANL] *)
(*  Status   : Unsatisfiable *)
(*  Rating   : 0.00 v2.1.0, 0.13 v2.0.0 *)
(*  Syntax   : Number of clauses     :   15 (   0 non-Horn;  15 unit;   1 RR) *)
(*             Number of atoms       :   15 (  15 equality) *)
(*             Maximal clause size   :    1 (   1 average) *)
(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)
(*             Number of functors    :    6 (   3 constant; 0-2 arity) *)
(*             Number of variables   :   24 (   0 singleton) *)
(*             Maximal term depth    :    3 (   2 average) *)
(*  Comments :  *)
(* -------------------------------------------------------------------------- *)
(* ----Include boolean algebra axioms for equality formulation  *)
(* Inclusion of: Axioms/BOO003-0.ax *)
(* -------------------------------------------------------------------------- *)
(*  File     : BOO003-0 : TPTP v3.1.1. Released v1.0.0. *)
(*  Domain   : Boolean Algebra *)
(*  Axioms   : Boolean algebra (equality) axioms *)
(*  Version  : [ANL] (equality) axioms. *)
(*  English  :  *)
(*  Refs     :  *)
(*  Source   : [ANL] *)
(*  Names    :  *)
(*  Status   :  *)
(*  Syntax   : Number of clauses    :   14 (   0 non-Horn;  14 unit;   0 RR) *)
(*             Number of literals   :   14 (  14 equality) *)
(*             Maximal clause size  :    1 (   1 average) *)
(*             Number of predicates :    1 (   0 propositional; 2-2 arity) *)
(*             Number of functors   :    5 (   2 constant; 0-2 arity) *)
(*             Number of variables  :   24 (   0 singleton) *)
(*             Maximal term depth   :    3 (   2 average) *)
(*  Comments :  *)
(* -------------------------------------------------------------------------- *)
(* -------------------------------------------------------------------------- *)
(* -------------------------------------------------------------------------- *)
theorem prove_a_plus_a_is_a:
 \forall Univ:Set.
\forall a:Univ.
\forall add:\forall _:Univ.\forall _:Univ.Univ.
\forall additive_identity:Univ.
\forall inverse:\forall _:Univ.Univ.
\forall multiplicative_identity:Univ.
\forall multiply:\forall _:Univ.\forall _:Univ.Univ.
\forall H0:\forall X:Univ.eq Univ (add additive_identity X) X.
\forall H1:\forall X:Univ.eq Univ (add X additive_identity) X.
\forall H2:\forall X:Univ.eq Univ (multiply multiplicative_identity X) X.
\forall H3:\forall X:Univ.eq Univ (multiply X multiplicative_identity) X.
\forall H4:\forall X:Univ.eq Univ (multiply (inverse X) X) additive_identity.
\forall H5:\forall X:Univ.eq Univ (multiply X (inverse X)) additive_identity.
\forall H6:\forall X:Univ.eq Univ (add (inverse X) X) multiplicative_identity.
\forall H7:\forall X:Univ.eq Univ (add X (inverse X)) multiplicative_identity.
\forall H8:\forall X:Univ.\forall Y:Univ.\forall Z:Univ.eq Univ (multiply X (add Y Z)) (add (multiply X Y) (multiply X Z)).
\forall H9:\forall X:Univ.\forall Y:Univ.\forall Z:Univ.eq Univ (multiply (add X Y) Z) (add (multiply X Z) (multiply Y Z)).
\forall H10:\forall X:Univ.\forall Y:Univ.\forall Z:Univ.eq Univ (add X (multiply Y Z)) (multiply (add X Y) (add X Z)).
\forall H11:\forall X:Univ.\forall Y:Univ.\forall Z:Univ.eq Univ (add (multiply X Y) Z) (multiply (add X Z) (add Y Z)).
\forall H12:\forall X:Univ.\forall Y:Univ.eq Univ (multiply X Y) (multiply Y X).
\forall H13:\forall X:Univ.\forall Y:Univ.eq Univ (add X Y) (add Y X).eq Univ (add a a) a
.
intros.
autobatch paramodulation timeout=100;
try assumption.
print proofterm.
qed.
(* -------------------------------------------------------------------------- *)

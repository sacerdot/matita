
include "logic/equality.ma".
(* Inclusion of: GRP001-2.p *)
(* -------------------------------------------------------------------------- *)
(*  File     : GRP001-2 : TPTP v3.1.1. Released v1.0.0. *)
(*  Domain   : Group Theory *)
(*  Problem  : X^2 = identity => commutativity *)
(*  Version  : [MOW76] (equality) axioms : Augmented. *)
(*  English  : If the square of every element is the identity, the system  *)
(*             is commutative. *)
(*  Refs     : [MOW76] McCharen et al. (1976), Problems and Experiments for a *)
(*           : [LO85]  Lusk & Overbeek (1985), Reasoning about Equality *)
(*           : [LW92]  Lusk & Wos (1992), Benchmark Problems in Which Equalit *)
(*  Source   : [ANL] *)
(*  Names    : GP1 [MOW76] *)
(*           : Problem 1 [LO85] *)
(*           : GT1 [LW92] *)
(*           : xsquared.ver2.in [ANL] *)
(*  Status   : Unsatisfiable *)
(*  Rating   : 0.00 v2.2.1, 0.22 v2.2.0, 0.29 v2.1.0, 0.25 v2.0.0 *)
(*  Syntax   : Number of clauses     :    8 (   0 non-Horn;   8 unit;   2 RR) *)
(*             Number of atoms       :    8 (   8 equality) *)
(*             Maximal clause size   :    1 (   1 average) *)
(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)
(*             Number of functors    :    6 (   4 constant; 0-2 arity) *)
(*             Number of variables   :    8 (   0 singleton) *)
(*             Maximal term depth    :    3 (   2 average) *)
(*  Comments :  *)
(* -------------------------------------------------------------------------- *)
(* ----Include equality group theory axioms  *)
(* Inclusion of: Axioms/GRP004-0.ax *)
(* -------------------------------------------------------------------------- *)
(*  File     : GRP004-0 : TPTP v3.1.1. Released v1.0.0. *)
(*  Domain   : Group Theory *)
(*  Axioms   : Group theory (equality) axioms *)
(*  Version  : [MOW76] (equality) axioms :  *)
(*             Reduced > Complete. *)
(*  English  :  *)
(*  Refs     : [MOW76] McCharen et al. (1976), Problems and Experiments for a *)
(*           : [Wos88] Wos (1988), Automated Reasoning - 33 Basic Research Pr *)
(*  Source   : [ANL] *)
(*  Names    :  *)
(*  Status   :  *)
(*  Syntax   : Number of clauses    :    3 (   0 non-Horn;   3 unit;   0 RR) *)
(*             Number of literals   :    3 (   3 equality) *)
(*             Maximal clause size  :    1 (   1 average) *)
(*             Number of predicates :    1 (   0 propositional; 2-2 arity) *)
(*             Number of functors   :    3 (   1 constant; 0-2 arity) *)
(*             Number of variables  :    5 (   0 singleton) *)
(*             Maximal term depth   :    3 (   2 average) *)
(*  Comments : [MOW76] also contains redundant right_identity and *)
(*             right_inverse axioms. *)
(*           : These axioms are also used in [Wos88] p.186, also with *)
(*             right_identity and right_inverse. *)
(* -------------------------------------------------------------------------- *)
(* ----For any x and y in the group x*y is also in the group. No clause  *)
(* ----is needed here since this is an instance of reflexivity  *)
(* ----There exists an identity element  *)
(* ----For any x in the group, there exists an element y such that x*y = y*x  *)
(* ----= identity. *)
(* ----The operation '*' is associative  *)
(* -------------------------------------------------------------------------- *)
(* -------------------------------------------------------------------------- *)
(* ----Redundant two axioms *)
theorem prove_b_times_a_is_c:
 \forall Univ:Set.
\forall a:Univ.
\forall b:Univ.
\forall c:Univ.
\forall identity:Univ.
\forall inverse:\forall _:Univ.Univ.
\forall multiply:\forall _:Univ.\forall _:Univ.Univ.
\forall H0:eq Univ (multiply a b) c.
\forall H1:\forall X:Univ.eq Univ (multiply X X) identity.
\forall H2:\forall X:Univ.eq Univ (multiply X (inverse X)) identity.
\forall H3:\forall X:Univ.eq Univ (multiply X identity) X.
\forall H4:\forall X:Univ.\forall Y:Univ.\forall Z:Univ.eq Univ (multiply (multiply X Y) Z) (multiply X (multiply Y Z)).
\forall H5:\forall X:Univ.eq Univ (multiply (inverse X) X) identity.
\forall H6:\forall X:Univ.eq Univ (multiply identity X) X.eq Univ (multiply b a) c
.
intros.
autobatch paramodulation timeout=100;
try assumption.
print proofterm.
qed.
(* -------------------------------------------------------------------------- *)

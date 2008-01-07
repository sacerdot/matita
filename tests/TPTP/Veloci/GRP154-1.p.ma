
include "logic/equality.ma".
(* Inclusion of: GRP154-1.p *)
(* -------------------------------------------------------------------------- *)
(*  File     : GRP154-1 : TPTP v3.1.1. Bugfixed v1.2.1. *)
(*  Domain   : Group Theory (Lattice Ordered) *)
(*  Problem  : Prove monotonicity axiom using the LUB transformation *)
(*  Version  : [Fuc94] (equality) axioms. *)
(*  English  : This problem proves the original mononicity axiom from the *)
(*             equational axiomatization. *)
(*  Refs     : [Fuc94] Fuchs (1994), The Application of Goal-Orientated Heuri *)
(*           : [Sch95] Schulz (1995), Explanation Based Learning for Distribu *)
(*  Source   : [Sch95] *)
(*  Names    : ax_mono1a [Sch95]  *)
(*  Status   : Unsatisfiable *)
(*  Rating   : 0.00 v2.0.0 *)
(*  Syntax   : Number of clauses     :   17 (   0 non-Horn;  17 unit;   2 RR) *)
(*             Number of atoms       :   17 (  17 equality) *)
(*             Maximal clause size   :    1 (   1 average) *)
(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)
(*             Number of functors    :    8 (   4 constant; 0-2 arity) *)
(*             Number of variables   :   33 (   2 singleton) *)
(*             Maximal term depth    :    3 (   2 average) *)
(*  Comments : ORDERING LPO inverse > product > greatest_lower_bound > *)
(*             least_upper_bound > identity > a > b > c *)
(*           : ORDERING LPO greatest_lower_bound > least_upper_bound >  *)
(*             inverse > product > identity > a > b > c *)
(*  Bugfixes : v1.2.1 - Duplicate axioms in GRP004-2.ax removed. *)
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
(* ----Include Lattice ordered group (equality) axioms *)
(* Inclusion of: Axioms/GRP004-2.ax *)
(* -------------------------------------------------------------------------- *)
(*  File     : GRP004-2 : TPTP v3.1.1. Bugfixed v1.2.0. *)
(*  Domain   : Group Theory (Lattice Ordered) *)
(*  Axioms   : Lattice ordered group (equality) axioms *)
(*  Version  : [Fuc94] (equality) axioms. *)
(*  English  :  *)
(*  Refs     : [Fuc94] Fuchs (1994), The Application of Goal-Orientated Heuri *)
(*           : [Sch95] Schulz (1995), Explanation Based Learning for Distribu *)
(*  Source   : [Sch95] *)
(*  Names    :  *)
(*  Status   :  *)
(*  Syntax   : Number of clauses    :   12 (   0 non-Horn;  12 unit;   0 RR) *)
(*             Number of literals   :   12 (  12 equality) *)
(*             Maximal clause size  :    1 (   1 average) *)
(*             Number of predicates :    1 (   0 propositional; 2-2 arity) *)
(*             Number of functors   :    3 (   0 constant; 2-2 arity) *)
(*             Number of variables  :   28 (   2 singleton) *)
(*             Maximal term depth   :    3 (   2 average) *)
(*  Comments : Requires GRP004-0.ax *)
(* -------------------------------------------------------------------------- *)
(* ----Specification of the least upper bound and greatest lower bound *)
(* ----Monotony of multiply *)
(* -------------------------------------------------------------------------- *)
(* -------------------------------------------------------------------------- *)
theorem prove_ax_mono1a:
 \forall Univ:Set.
\forall a:Univ.
\forall b:Univ.
\forall c:Univ.
\forall greatest_lower_bound:\forall _:Univ.\forall _:Univ.Univ.
\forall identity:Univ.
\forall inverse:\forall _:Univ.Univ.
\forall least_upper_bound:\forall _:Univ.\forall _:Univ.Univ.
\forall multiply:\forall _:Univ.\forall _:Univ.Univ.
\forall H0:eq Univ (least_upper_bound a b) b.
\forall H1:\forall X:Univ.\forall Y:Univ.\forall Z:Univ.eq Univ (multiply (greatest_lower_bound Y Z) X) (greatest_lower_bound (multiply Y X) (multiply Z X)).
\forall H2:\forall X:Univ.\forall Y:Univ.\forall Z:Univ.eq Univ (multiply (least_upper_bound Y Z) X) (least_upper_bound (multiply Y X) (multiply Z X)).
\forall H3:\forall X:Univ.\forall Y:Univ.\forall Z:Univ.eq Univ (multiply X (greatest_lower_bound Y Z)) (greatest_lower_bound (multiply X Y) (multiply X Z)).
\forall H4:\forall X:Univ.\forall Y:Univ.\forall Z:Univ.eq Univ (multiply X (least_upper_bound Y Z)) (least_upper_bound (multiply X Y) (multiply X Z)).
\forall H5:\forall X:Univ.\forall Y:Univ.eq Univ (greatest_lower_bound X (least_upper_bound X Y)) X.
\forall H6:\forall X:Univ.\forall Y:Univ.eq Univ (least_upper_bound X (greatest_lower_bound X Y)) X.
\forall H7:\forall X:Univ.eq Univ (greatest_lower_bound X X) X.
\forall H8:\forall X:Univ.eq Univ (least_upper_bound X X) X.
\forall H9:\forall X:Univ.\forall Y:Univ.\forall Z:Univ.eq Univ (least_upper_bound X (least_upper_bound Y Z)) (least_upper_bound (least_upper_bound X Y) Z).
\forall H10:\forall X:Univ.\forall Y:Univ.\forall Z:Univ.eq Univ (greatest_lower_bound X (greatest_lower_bound Y Z)) (greatest_lower_bound (greatest_lower_bound X Y) Z).
\forall H11:\forall X:Univ.\forall Y:Univ.eq Univ (least_upper_bound X Y) (least_upper_bound Y X).
\forall H12:\forall X:Univ.\forall Y:Univ.eq Univ (greatest_lower_bound X Y) (greatest_lower_bound Y X).
\forall H13:\forall X:Univ.\forall Y:Univ.\forall Z:Univ.eq Univ (multiply (multiply X Y) Z) (multiply X (multiply Y Z)).
\forall H14:\forall X:Univ.eq Univ (multiply (inverse X) X) identity.
\forall H15:\forall X:Univ.eq Univ (multiply identity X) X.eq Univ (least_upper_bound (multiply a c) (multiply b c)) (multiply b c)
.
intros.
autobatch paramodulation timeout=100;
try assumption.
print proofterm.
qed.
(* -------------------------------------------------------------------------- *)

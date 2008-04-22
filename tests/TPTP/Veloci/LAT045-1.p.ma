
include "logic/equality.ma".
(* Inclusion of: LAT045-1.p *)
(* -------------------------------------------------------------------------- *)
(*  File     : LAT045-1 : TPTP v3.1.1. Released v2.5.0. *)
(*  Domain   : Lattice Theory *)
(*  Problem  : Lattice orthomodular law from modular lattice *)
(*  Version  : [McC88] (equality) axioms. *)
(*  English  :  *)
(*  Refs     : [McC88] McCune (1988), Challenge Equality Problems in Lattice  *)
(*           : [RW01]  Rose & Wilkinson (2001), Application of Model Search *)
(*  Source   : [RW01] *)
(*  Names    : eqp-f.in [RW01] *)
(*  Status   : Unsatisfiable *)
(*  Rating   : 0.07 v3.1.0, 0.11 v2.7.0, 0.00 v2.5.0 *)
(*  Syntax   : Number of clauses     :   15 (   0 non-Horn;  15 unit;   1 RR) *)
(*             Number of atoms       :   15 (  15 equality) *)
(*             Maximal clause size   :    1 (   1 average) *)
(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)
(*             Number of functors    :    7 (   4 constant; 0-2 arity) *)
(*             Number of variables   :   26 (   2 singleton) *)
(*             Maximal term depth    :    4 (   2 average) *)
(*  Comments :  *)
(* -------------------------------------------------------------------------- *)
(* ----Include lattice axioms  *)
(* Inclusion of: Axioms/LAT001-0.ax *)
(* -------------------------------------------------------------------------- *)
(*  File     : LAT001-0 : TPTP v3.1.1. Released v1.0.0. *)
(*  Domain   : Lattice Theory *)
(*  Axioms   : Lattice theory (equality) axioms *)
(*  Version  : [McC88] (equality) axioms. *)
(*  English  :  *)
(*  Refs     : [Bum65] Bumcroft (1965), Proceedings of the Glasgow Mathematic *)
(*           : [McC88] McCune (1988), Challenge Equality Problems in Lattice  *)
(*           : [Wos88] Wos (1988), Automated Reasoning - 33 Basic Research Pr *)
(*  Source   : [McC88] *)
(*  Names    :  *)
(*  Status   :  *)
(*  Syntax   : Number of clauses    :    8 (   0 non-Horn;   8 unit;   0 RR) *)
(*             Number of literals   :    8 (   8 equality) *)
(*             Maximal clause size  :    1 (   1 average) *)
(*             Number of predicates :    1 (   0 propositional; 2-2 arity) *)
(*             Number of functors   :    2 (   0 constant; 2-2 arity) *)
(*             Number of variables  :   16 (   2 singleton) *)
(*             Maximal term depth   :    3 (   2 average) *)
(*  Comments :  *)
(* -------------------------------------------------------------------------- *)
(* ----The following 8 clauses characterise lattices  *)
(* -------------------------------------------------------------------------- *)
(* -------------------------------------------------------------------------- *)
(* ----Compatibility (6) *)
(* ----Invertability (5) *)
(* ----Modular law (7) *)
(* ----Denial of orthomodular law (8) *)
theorem prove_orthomodular_law:
 \forall Univ:Set.
\forall a:Univ.
\forall b:Univ.
\forall complement:\forall _:Univ.Univ.
\forall join:\forall _:Univ.\forall _:Univ.Univ.
\forall meet:\forall _:Univ.\forall _:Univ.Univ.
\forall n0:Univ.
\forall n1:Univ.
\forall H0:\forall X:Univ.\forall Y:Univ.\forall Z:Univ.eq Univ (join X (meet Y (join X Z))) (meet (join X Y) (join X Z)).
\forall H1:\forall X:Univ.eq Univ (complement (complement X)) X.
\forall H2:\forall X:Univ.eq Univ (meet (complement X) X) n0.
\forall H3:\forall X:Univ.eq Univ (join (complement X) X) n1.
\forall H4:\forall X:Univ.\forall Y:Univ.eq Univ (complement (meet X Y)) (join (complement X) (complement Y)).
\forall H5:\forall X:Univ.\forall Y:Univ.eq Univ (complement (join X Y)) (meet (complement X) (complement Y)).
\forall H6:\forall X:Univ.\forall Y:Univ.\forall Z:Univ.eq Univ (join (join X Y) Z) (join X (join Y Z)).
\forall H7:\forall X:Univ.\forall Y:Univ.\forall Z:Univ.eq Univ (meet (meet X Y) Z) (meet X (meet Y Z)).
\forall H8:\forall X:Univ.\forall Y:Univ.eq Univ (join X Y) (join Y X).
\forall H9:\forall X:Univ.\forall Y:Univ.eq Univ (meet X Y) (meet Y X).
\forall H10:\forall X:Univ.\forall Y:Univ.eq Univ (join X (meet X Y)) X.
\forall H11:\forall X:Univ.\forall Y:Univ.eq Univ (meet X (join X Y)) X.
\forall H12:\forall X:Univ.eq Univ (join X X) X.
\forall H13:\forall X:Univ.eq Univ (meet X X) X.eq Univ (join a (meet (complement a) (join a b))) (join a b)
.
intros.
autobatch paramodulation timeout=100;
try assumption.
print proofterm.
qed.
(* -------------------------------------------------------------------------- *)

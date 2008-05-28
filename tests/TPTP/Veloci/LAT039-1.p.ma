
include "logic/equality.ma".
(* Inclusion of: LAT039-1.p *)
(* -------------------------------------------------------------------------- *)
(*  File     : LAT039-1 : TPTP v3.1.1. Released v2.4.0. *)
(*  Domain   : Lattice Theory *)
(*  Problem  : Every distributive lattice is modular *)
(*  Version  : [McC88] (equality) axioms. *)
(*             Theorem formulation : Modularity is expressed by:  *)
(*             x <= y -> x v (y & z) = y & (x v z) *)
(*  English  : *)
(*  Refs     : [DeN00] DeNivelle (2000), Email to G. Sutcliffe *)
(*             [McC88] McCune (1988), Challenge Equality Problems in Lattice *)
(*  Source   : [DeN00] *)
(*  Names    : lattice-mod-2 [DeN00] *)
(*  Status   : Unsatisfiable *)
(*  Rating   : 0.00 v2.4.0 *)
(*  Syntax   : Number of clauses     :   12 (   0 non-Horn;  12 unit;   2 RR) *)
(*             Number of atoms       :   12 (  12 equality) *)
(*             Maximal clause size   :    1 (   1 average) *)
(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)
(*             Number of functors    :    5 (   3 constant; 0-2 arity) *)
(*             Number of variables   :   22 (   2 singleton) *)
(*             Maximal term depth    :    3 (   2 average) *)
(*  Comments :  *)
(* -------------------------------------------------------------------------- *)
(* ----Include lattice theory axioms *)
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
theorem rhs:
 \forall Univ:Set.
\forall join:\forall _:Univ.\forall _:Univ.Univ.
\forall meet:\forall _:Univ.\forall _:Univ.Univ.
\forall xx:Univ.
\forall yy:Univ.
\forall zz:Univ.
\forall H0:eq Univ (join xx yy) yy.
\forall H1:\forall X:Univ.\forall Y:Univ.\forall Z:Univ.eq Univ (meet X (join Y Z)) (join (meet X Y) (meet X Z)).
\forall H2:\forall X:Univ.\forall Y:Univ.\forall Z:Univ.eq Univ (join X (meet Y Z)) (meet (join X Y) (join X Z)).
\forall H3:\forall X:Univ.\forall Y:Univ.\forall Z:Univ.eq Univ (join (join X Y) Z) (join X (join Y Z)).
\forall H4:\forall X:Univ.\forall Y:Univ.\forall Z:Univ.eq Univ (meet (meet X Y) Z) (meet X (meet Y Z)).
\forall H5:\forall X:Univ.\forall Y:Univ.eq Univ (join X Y) (join Y X).
\forall H6:\forall X:Univ.\forall Y:Univ.eq Univ (meet X Y) (meet Y X).
\forall H7:\forall X:Univ.\forall Y:Univ.eq Univ (join X (meet X Y)) X.
\forall H8:\forall X:Univ.\forall Y:Univ.eq Univ (meet X (join X Y)) X.
\forall H9:\forall X:Univ.eq Univ (join X X) X.
\forall H10:\forall X:Univ.eq Univ (meet X X) X.eq Univ (join xx (meet yy zz)) (meet yy (join xx zz))
.
intros.
autobatch paramodulation timeout=100;
try assumption.
print proofterm.
qed.
(* -------------------------------------------------------------------------- *)

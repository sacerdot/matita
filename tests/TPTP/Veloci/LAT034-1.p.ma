
include "logic/equality.ma".
(* Inclusion of: LAT034-1.p *)
(* -------------------------------------------------------------------------- *)
(*  File     : LAT034-1 : TPTP v3.1.1. Bugfixed v2.5.0. *)
(*  Domain   : Lattice Theory *)
(*  Problem  : Idempotency of meet *)
(*  Version  : [McC88] (equality) axioms. *)
(*  English  : *)
(*  Refs     : [DeN00] DeNivelle (2000), Email to G. Sutcliffe *)
(*             [McC88] McCune (1988), Challenge Equality Problems in Lattice *)
(*  Source   : [DeN00] *)
(*  Names    : idemp_of_meet [DeN00] *)
(*  Status   : Unsatisfiable *)
(*  Rating   : 0.00 v2.5.0 *)
(*  Syntax   : Number of clauses     :    7 (   0 non-Horn;   7 unit;   1 RR) *)
(*             Number of atoms       :    7 (   7 equality) *)
(*             Maximal clause size   :    1 (   1 average) *)
(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)
(*             Number of functors    :    3 (   1 constant; 0-2 arity) *)
(*             Number of variables   :   14 (   2 singleton) *)
(*             Maximal term depth    :    3 (   2 average) *)
(*  Comments :  *)
(*  Bugfixes : v2.5.0 - Used axioms without the conjecture *)
(* -------------------------------------------------------------------------- *)
(* ----Include lattice theory axioms *)
(* include('Axioms/LAT001-0.ax'). *)
(* -------------------------------------------------------------------------- *)
theorem idempotence_of_meet:
 \forall Univ:Set.
\forall join:\forall _:Univ.\forall _:Univ.Univ.
\forall meet:\forall _:Univ.\forall _:Univ.Univ.
\forall xx:Univ.
\forall H0:\forall X:Univ.\forall Y:Univ.\forall Z:Univ.eq Univ (join (join X Y) Z) (join X (join Y Z)).
\forall H1:\forall X:Univ.\forall Y:Univ.\forall Z:Univ.eq Univ (meet (meet X Y) Z) (meet X (meet Y Z)).
\forall H2:\forall X:Univ.\forall Y:Univ.eq Univ (join X Y) (join Y X).
\forall H3:\forall X:Univ.\forall Y:Univ.eq Univ (meet X Y) (meet Y X).
\forall H4:\forall X:Univ.\forall Y:Univ.eq Univ (join X (meet X Y)) X.
\forall H5:\forall X:Univ.\forall Y:Univ.eq Univ (meet X (join X Y)) X.eq Univ (meet xx xx) xx
.
intros.
autobatch paramodulation timeout=100;
try assumption.
print proofterm.
qed.
(* -------------------------------------------------------------------------- *)

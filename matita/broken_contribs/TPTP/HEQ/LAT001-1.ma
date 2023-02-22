set "baseuri" "cic:/matita/TPTP/LAT001-1".
include "logic/equality.ma".

(* Inclusion of: LAT001-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : LAT001-1 : TPTP v3.2.0. Released v1.0.0. *)

(*  Domain   : Lattice Theory *)

(*  Problem  : If X' = U v V and Y' = U ^ V, then U' = X v (Y ^ V) *)

(*  Version  : [McC88] (equality) axioms. *)

(*  English  : The theorem states that there is a complement of "a" in a *)

(*             modular lattice with 0 and 1. *)

(*  Refs     : [Bum65] Bumcroft (1965), Proceedings of the Glasgow Mathematic *)

(*           : [GO+69] Guard et al. (1969), Semi-Automated Mathematics *)

(*           : [McC88] McCune (1988), Challenge Equality Problems in Lattice  *)

(*  Source   : [McC88] *)

(*  Names    : L1a [McC88] *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.71 v3.2.0, 0.57 v3.1.0, 0.78 v2.7.0, 0.83 v2.6.0, 0.86 v2.5.0, 1.00 v2.0.0 *)

(*  Syntax   : Number of clauses     :   19 (   0 non-Horn;  15 unit;   6 RR) *)

(*             Number of atoms       :   24 (  18 equality) *)

(*             Maximal clause size   :    3 (   1 average) *)

(*             Number of predicates  :    2 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    8 (   6 constant; 0-2 arity) *)

(*             Number of variables   :   29 (   4 singleton) *)

(*             Maximal term depth    :    3 (   2 average) *)

(*  Comments : No further information is available from [McC88] or [GO+69] *)

(*             about [Bum65]. *)

(* -------------------------------------------------------------------------- *)

(* ----Include lattice axioms  *)

(* Inclusion of: Axioms/LAT001-0.ax *)

(* -------------------------------------------------------------------------- *)

(*  File     : LAT001-0 : TPTP v3.2.0. Released v1.0.0. *)

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

(* ----Include modular lattice axioms  *)

(* Inclusion of: Axioms/LAT001-1.ax *)

(* -------------------------------------------------------------------------- *)

(*  File     : LAT001-1 : TPTP v3.2.0. Released v1.0.0. *)

(*  Domain   : Lattice Theory *)

(*  Axioms   : Lattice theory modularity (equality) axioms *)

(*  Version  : [McC88] (equality) axioms. *)

(*  English  :  *)

(*  Refs     : [Bum65] Bumcroft (1965), Proceedings of the Glasgow Mathematic *)

(*           : [McC88] McCune (1988), Challenge Equality Problems in Lattice  *)

(*           : [Wos88] Wos (1988), Automated Reasoning - 33 Basic Research Pr *)

(*  Source   : [McC88] *)

(*  Names    :  *)

(*  Status   :  *)

(*  Syntax   : Number of clauses    :    5 (   0 non-Horn;   4 unit;   0 RR) *)

(*             Number of literals   :    6 (   6 equality) *)

(*             Maximal clause size  :    2 (   1 average) *)

(*             Number of predicates :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors   :    4 (   2 constant; 0-2 arity) *)

(*             Number of variables  :    7 (   2 singleton) *)

(*             Maximal term depth   :    3 (   2 average) *)

(*  Comments : Requires LAT001-0.ax *)

(*           : These axioms, with 4 extra redundant axioms about 0 & 1, are  *)

(*             used in [Wos88] p.217. *)

(* -------------------------------------------------------------------------- *)

(* ----Include 1 and 0 in the lattice  *)

(* ----Require the lattice to be modular  *)

(* -------------------------------------------------------------------------- *)

(* ----Include definition of complement  *)

(* Inclusion of: Axioms/LAT001-2.ax *)

(* -------------------------------------------------------------------------- *)

(*  File     : LAT001-2 : TPTP v3.2.0. Released v1.0.0. *)

(*  Domain   : Lattice Theory *)

(*  Axioms   : Lattice theory complement (equality) axioms *)

(*  Version  : [McC88] (equality) axioms. *)

(*  English  :  *)

(*  Refs     : [Bum65] Bumcroft (1965), Proceedings of the Glasgow Mathematic *)

(*           : [McC88] McCune (1988), Challenge Equality Problems in Lattice  *)

(*  Source   : [McC88] *)

(*  Names    :  *)

(*  Status   :  *)

(*  Syntax   : Number of clauses    :    3 (   0 non-Horn;   0 unit;   3 RR) *)

(*             Number of literals   :    7 (   4 equality) *)

(*             Maximal clause size  :    3 (   2 average) *)

(*             Number of predicates :    2 (   0 propositional; 2-2 arity) *)

(*             Number of functors   :    4 (   2 constant; 0-2 arity) *)

(*             Number of variables  :    6 (   0 singleton) *)

(*             Maximal term depth   :    2 (   1 average) *)

(*  Comments : Requires LAT001-0.ax *)

(* -------------------------------------------------------------------------- *)

(* ----Definition of complement  *)

(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
theorem prove_complememt:
 ∀Univ:Set.∀X:Univ.∀Y:Univ.∀Z:Univ.∀a:Univ.∀b:Univ.∀complement:∀_:Univ.∀_:Univ.Prop.∀join:∀_:Univ.∀_:Univ.Univ.∀meet:∀_:Univ.∀_:Univ.Univ.∀n0:Univ.∀n1:Univ.∀r1:Univ.∀r2:Univ.∀H0:complement r2 (meet a b).∀H1:complement r1 (join a b).∀H2:∀X:Univ.∀Y:Univ.∀_:eq Univ (join X Y) n1.∀_:eq Univ (meet X Y) n0.complement X Y.∀H3:∀X:Univ.∀Y:Univ.∀_:complement X Y.eq Univ (join X Y) n1.∀H4:∀X:Univ.∀Y:Univ.∀_:complement X Y.eq Univ (meet X Y) n0.∀H5:∀X:Univ.∀Y:Univ.∀Z:Univ.∀_:eq Univ (meet X Z) X.eq Univ (meet Z (join X Y)) (join X (meet Y Z)).∀H6:∀X:Univ.eq Univ (join X n1) n1.∀H7:∀X:Univ.eq Univ (meet X n1) X.∀H8:∀X:Univ.eq Univ (join X n0) X.∀H9:∀X:Univ.eq Univ (meet X n0) n0.∀H10:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (join (join X Y) Z) (join X (join Y Z)).∀H11:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (meet (meet X Y) Z) (meet X (meet Y Z)).∀H12:∀X:Univ.∀Y:Univ.eq Univ (join X Y) (join Y X).∀H13:∀X:Univ.∀Y:Univ.eq Univ (meet X Y) (meet Y X).∀H14:∀X:Univ.∀Y:Univ.eq Univ (join X (meet X Y)) X.∀H15:∀X:Univ.∀Y:Univ.eq Univ (meet X (join X Y)) X.∀H16:∀X:Univ.eq Univ (join X X) X.∀H17:∀X:Univ.eq Univ (meet X X) X.complement a (join r1 (meet r2 b))
.
intros.
autobatch depth=5 width=5 size=20 timeout=10;
try assumption.
print proofterm.
qed.

(* -------------------------------------------------------------------------- *)

set "baseuri" "cic:/matita/TPTP/LAT005-3".
include "logic/equality.ma".

(* Inclusion of: LAT005-3.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : LAT005-3 : TPTP v3.2.0. Released v1.0.0. *)

(*  Domain   : Lattice Theory *)

(*  Problem  : SAM's lemma *)

(*  Version  : [McC88] (equality) axioms. *)

(*  English  : Let L be a modular lattice with 0 and 1.  Suppose that A and  *)

(*             B are elements of L such that (A v B) and (A ^ B) both have  *)

(*             not necessarily unique complements. Then, (A v B)' =  *)

(*             ((A v B)' v ((A ^ B)' ^ B)) ^ ((A v B)' v ((A ^ B)' ^ A)). *)

(*  Refs     : [GO+69] Guard et al. (1969), Semi-Automated Mathematics *)

(*           : [McC88] McCune (1988), Challenge Equality Problems in Lattice  *)

(*  Source   : [McC88] *)

(*  Names    : SAM's lemma [McC88] *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.43 v3.2.0, 0.14 v3.1.0, 0.44 v2.7.0, 0.50 v2.6.0, 0.43 v2.5.0, 0.80 v2.4.0, 1.00 v2.3.0, 0.83 v2.2.1, 0.89 v2.2.0, 0.86 v2.1.0, 1.00 v2.0.0 *)

(*  Syntax   : Number of clauses     :   19 (   0 non-Horn;  15 unit;   6 RR) *)

(*             Number of atoms       :   24 (  19 equality) *)

(*             Maximal clause size   :    3 (   1 average) *)

(*             Number of predicates  :    2 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    8 (   6 constant; 0-2 arity) *)

(*             Number of variables   :   29 (   4 singleton) *)

(*             Maximal term depth    :    4 (   2 average) *)

(*  Comments : [McC88] specifies that the axioms for complement should not be *)

(*             included ("clauses 1-13 from axioms"). However, if this makes *)

(*             clauses 87 and 88 pure. I have assumed a typo in the paper and *)

(*             included axioms 14-16. *)

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
theorem prove_lemma:
 ∀Univ:Set.∀X:Univ.∀Y:Univ.∀Z:Univ.∀a:Univ.∀b:Univ.∀complement:∀_:Univ.∀_:Univ.Prop.∀join:∀_:Univ.∀_:Univ.Univ.∀meet:∀_:Univ.∀_:Univ.Univ.∀n0:Univ.∀n1:Univ.∀r1:Univ.∀r2:Univ.∀H0:complement r2 (meet a b).∀H1:complement r1 (join a b).∀H2:∀X:Univ.∀Y:Univ.∀_:eq Univ (join X Y) n1.∀_:eq Univ (meet X Y) n0.complement X Y.∀H3:∀X:Univ.∀Y:Univ.∀_:complement X Y.eq Univ (join X Y) n1.∀H4:∀X:Univ.∀Y:Univ.∀_:complement X Y.eq Univ (meet X Y) n0.∀H5:∀X:Univ.∀Y:Univ.∀Z:Univ.∀_:eq Univ (meet X Z) X.eq Univ (meet Z (join X Y)) (join X (meet Y Z)).∀H6:∀X:Univ.eq Univ (join X n1) n1.∀H7:∀X:Univ.eq Univ (meet X n1) X.∀H8:∀X:Univ.eq Univ (join X n0) X.∀H9:∀X:Univ.eq Univ (meet X n0) n0.∀H10:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (join (join X Y) Z) (join X (join Y Z)).∀H11:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (meet (meet X Y) Z) (meet X (meet Y Z)).∀H12:∀X:Univ.∀Y:Univ.eq Univ (join X Y) (join Y X).∀H13:∀X:Univ.∀Y:Univ.eq Univ (meet X Y) (meet Y X).∀H14:∀X:Univ.∀Y:Univ.eq Univ (join X (meet X Y)) X.∀H15:∀X:Univ.∀Y:Univ.eq Univ (meet X (join X Y)) X.∀H16:∀X:Univ.eq Univ (join X X) X.∀H17:∀X:Univ.eq Univ (meet X X) X.eq Univ r1 (meet (join r1 (meet r2 b)) (join r1 (meet r2 a)))
.
intros.
autobatch depth=5 width=5 size=20 timeout=10;
try assumption.
print proofterm.
qed.

(* -------------------------------------------------------------------------- *)

include "logic/equality.ma".

(* Inclusion of: LAT047-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : LAT047-1 : TPTP v3.7.0. Released v2.5.0. *)

(*  Domain   : Lattice Theory *)

(*  Problem  : Lattice is not modular lattice *)

(*  Version  : [McC88] (equality) axioms. *)

(*  English  :  *)

(*  Refs     : [McC88] McCune (1988), Challenge Equality Problems in Lattice  *)

(*           : [RW01]  Rose & Wilkinson (2001), Application of Model Search *)

(*  Source   : [RW01] *)

(*  Names    : mace-b.in [RW01] *)

(*  Status   : Satisfiable *)

(*  Rating   : 0.33 v3.2.0, 0.67 v3.1.0, 0.33 v2.5.0 *)

(*  Syntax   : Number of clauses     :    9 (   0 non-Horn;   9 unit;   1 RR) *)

(*             Number of atoms       :    9 (   9 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    5 (   3 constant; 0-2 arity) *)

(*             Number of variables   :   16 (   2 singleton) *)

(*             Maximal term depth    :    4 (   2 average) *)

(*  Comments :  *)

(* -------------------------------------------------------------------------- *)

(* ----Include lattice axioms  *)

(* Inclusion of: Axioms/LAT001-0.ax *)

(* -------------------------------------------------------------------------- *)

(*  File     : LAT001-0 : TPTP v3.7.0. Released v1.0.0. *)

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

(*             Number of atoms      :    8 (   8 equality) *)

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

(* ----Denial of modularity (7) *)
ntheorem prove_modularity:
 (∀Univ:Type.∀X:Univ.∀Y:Univ.∀Z:Univ.
∀a:Univ.
∀b:Univ.
∀c:Univ.
∀join:∀_:Univ.∀_:Univ.Univ.
∀meet:∀_:Univ.∀_:Univ.Univ.
∀H0:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (join (join X Y) Z) (join X (join Y Z)).
∀H1:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (meet (meet X Y) Z) (meet X (meet Y Z)).
∀H2:∀X:Univ.∀Y:Univ.eq Univ (join X Y) (join Y X).
∀H3:∀X:Univ.∀Y:Univ.eq Univ (meet X Y) (meet Y X).
∀H4:∀X:Univ.∀Y:Univ.eq Univ (join X (meet X Y)) X.
∀H5:∀X:Univ.∀Y:Univ.eq Univ (meet X (join X Y)) X.
∀H6:∀X:Univ.eq Univ (join X X) X.
∀H7:∀X:Univ.eq Univ (meet X X) X.eq Univ (join a (meet b (join a c))) (meet (join a b) (join a c)))
.
#Univ ##.
#X ##.
#Y ##.
#Z ##.
#a ##.
#b ##.
#c ##.
#join ##.
#meet ##.
#H0 ##.
#H1 ##.
#H2 ##.
#H3 ##.
#H4 ##.
#H5 ##.
#H6 ##.
#H7 ##.
nauto by H0,H1,H2,H3,H4,H5,H6,H7 ##;
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)

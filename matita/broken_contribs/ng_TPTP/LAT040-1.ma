include "logic/equality.ma".

(* Inclusion of: LAT040-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : LAT040-1 : TPTP v3.7.0. Released v2.4.0. *)

(*  Domain   : Lattice Theory *)

(*  Problem  : Another simplification rule for distributive lattices *)

(*  Version  : [McC88] (equality) axioms. *)

(*  English  : In every distributive lattice the simplification rule holds: *)

(*             forall x, y, z: (x v y = x v z, x & y = x & z -> y = z ). *)

(*  Refs     : [DeN00] DeNivelle (2000), Email to G. Sutcliffe *)

(*             [McC88] McCune (1988), Challenge Equality Problems in Lattice *)

(*  Source   : [DeN00] *)

(*  Names    : lattice-simpl [DeN00] *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.00 v2.4.0 *)

(*  Syntax   : Number of clauses     :   13 (   0 non-Horn;  13 unit;   3 RR) *)

(*             Number of atoms       :   13 (  13 equality) *)

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
ntheorem rhs:
 (∀Univ:Type.∀X:Univ.∀Y:Univ.∀Z:Univ.
∀join:∀_:Univ.∀_:Univ.Univ.
∀meet:∀_:Univ.∀_:Univ.Univ.
∀xx:Univ.
∀yy:Univ.
∀zz:Univ.
∀H0:eq Univ (meet xx yy) (meet xx zz).
∀H1:eq Univ (join xx yy) (join xx zz).
∀H2:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (meet X (join Y Z)) (join (meet X Y) (meet X Z)).
∀H3:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (join X (meet Y Z)) (meet (join X Y) (join X Z)).
∀H4:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (join (join X Y) Z) (join X (join Y Z)).
∀H5:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (meet (meet X Y) Z) (meet X (meet Y Z)).
∀H6:∀X:Univ.∀Y:Univ.eq Univ (join X Y) (join Y X).
∀H7:∀X:Univ.∀Y:Univ.eq Univ (meet X Y) (meet Y X).
∀H8:∀X:Univ.∀Y:Univ.eq Univ (join X (meet X Y)) X.
∀H9:∀X:Univ.∀Y:Univ.eq Univ (meet X (join X Y)) X.
∀H10:∀X:Univ.eq Univ (join X X) X.
∀H11:∀X:Univ.eq Univ (meet X X) X.eq Univ yy zz)
.
#Univ ##.
#X ##.
#Y ##.
#Z ##.
#join ##.
#meet ##.
#xx ##.
#yy ##.
#zz ##.
#H0 ##.
#H1 ##.
#H2 ##.
#H3 ##.
#H4 ##.
#H5 ##.
#H6 ##.
#H7 ##.
#H8 ##.
#H9 ##.
#H10 ##.
#H11 ##.
nauto by H0,H1,H2,H3,H4,H5,H6,H7,H8,H9,H10,H11 ##;
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)

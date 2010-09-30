include "logic/equality.ma".

(* Inclusion of: LAT063-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : LAT063-1 : TPTP v3.7.0. Released v2.5.0. *)

(*  Domain   : Lattice Theory *)

(*  Problem  : E62 does not necessarily hold in ortholattices *)

(*  Version  : [EF+02] axioms. *)

(*  English  :  *)

(*  Refs     : [EF+02] Ernst et al. (2002), More First-order Test Problems in *)

(*  Source   : [EF+02] *)

(*  Names    : ol-e62 [EF+02] *)

(*  Status   : Satisfiable *)

(*  Rating   : 0.33 v3.2.0, 0.67 v3.1.0, 0.33 v2.6.0, 0.67 v2.5.0 *)

(*  Syntax   : Number of clauses     :   12 (   0 non-Horn;  12 unit;   1 RR) *)

(*             Number of atoms       :   12 (  12 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    7 (   4 constant; 0-2 arity) *)

(*             Number of variables   :   20 (   2 singleton) *)

(*             Maximal term depth    :    6 (   2 average) *)

(*  Comments :  *)

(* -------------------------------------------------------------------------- *)

(* ----Include lattice axioms *)

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

(* ----Ortholattice axioms *)

(* ----Denial of E62 *)
ntheorem prove_e62:
 (∀Univ:Type.∀A:Univ.∀B:Univ.∀X:Univ.∀Y:Univ.∀Z:Univ.
∀a:Univ.
∀b:Univ.
∀complement:∀_:Univ.Univ.
∀join:∀_:Univ.∀_:Univ.Univ.
∀meet:∀_:Univ.∀_:Univ.Univ.
∀n0:Univ.
∀n1:Univ.
∀H0:∀A:Univ.∀B:Univ.eq Univ (meet A B) (complement (join (complement A) (complement B))).
∀H1:∀A:Univ.eq Univ (meet (complement A) A) n0.
∀H2:∀A:Univ.eq Univ (join (complement A) A) n1.
∀H3:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (join (join X Y) Z) (join X (join Y Z)).
∀H4:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (meet (meet X Y) Z) (meet X (meet Y Z)).
∀H5:∀X:Univ.∀Y:Univ.eq Univ (join X Y) (join Y X).
∀H6:∀X:Univ.∀Y:Univ.eq Univ (meet X Y) (meet Y X).
∀H7:∀X:Univ.∀Y:Univ.eq Univ (join X (meet X Y)) X.
∀H8:∀X:Univ.∀Y:Univ.eq Univ (meet X (join X Y)) X.
∀H9:∀X:Univ.eq Univ (join X X) X.
∀H10:∀X:Univ.eq Univ (meet X X) X.eq Univ (meet a (join b (meet a (join (complement a) (meet a b))))) (meet a (join (complement a) (meet a b))))
.
#Univ ##.
#A ##.
#B ##.
#X ##.
#Y ##.
#Z ##.
#a ##.
#b ##.
#complement ##.
#join ##.
#meet ##.
#n0 ##.
#n1 ##.
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
nauto by H0,H1,H2,H3,H4,H5,H6,H7,H8,H9,H10 ##;
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)

include "logic/equality.ma".

(* Inclusion of: LAT105-1.p *)

(* ------------------------------------------------------------------------------ *)

(*  File     : LAT105-1 : TPTP v3.7.0. Released v3.1.0. *)

(*  Domain   : Lattice Theory *)

(*  Problem  : Huntington equation H10 is independent of H21 *)

(*  Version  : [McC05] (equality) axioms : Especial. *)

(*  English  : Show that Huntington equation H21 does not imply Huntington  *)

(*             equation H10 in lattice theory. *)

(*  Refs     : [McC05] McCune (2005), Email to Geoff Sutcliffe *)

(*  Source   : [McC05] *)

(*  Names    :  *)

(*  Status   : Satisfiable *)

(*  Rating   : 0.33 v3.2.0, 0.67 v3.1.0 *)

(*  Syntax   : Number of clauses     :   10 (   0 non-Horn;  10 unit;   1 RR) *)

(*             Number of atoms       :   10 (  10 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    5 (   3 constant; 0-2 arity) *)

(*             Number of variables   :   19 (   2 singleton) *)

(*             Maximal term depth    :    6 (   3 average) *)

(*  Comments :  *)

(* ------------------------------------------------------------------------------ *)

(* ----Include Lattice theory (equality) axioms *)

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

(* ------------------------------------------------------------------------------ *)
ntheorem prove_H10:
 (∀Univ:Type.∀X:Univ.∀Y:Univ.∀Z:Univ.
∀a:Univ.
∀b:Univ.
∀c:Univ.
∀join:∀_:Univ.∀_:Univ.Univ.
∀meet:∀_:Univ.∀_:Univ.Univ.
∀H0:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (join (meet X Y) (meet X Z)) (meet X (join (meet Y (join X (meet Y Z))) (meet Z (join X Y)))).
∀H1:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (join (join X Y) Z) (join X (join Y Z)).
∀H2:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (meet (meet X Y) Z) (meet X (meet Y Z)).
∀H3:∀X:Univ.∀Y:Univ.eq Univ (join X Y) (join Y X).
∀H4:∀X:Univ.∀Y:Univ.eq Univ (meet X Y) (meet Y X).
∀H5:∀X:Univ.∀Y:Univ.eq Univ (join X (meet X Y)) X.
∀H6:∀X:Univ.∀Y:Univ.eq Univ (meet X (join X Y)) X.
∀H7:∀X:Univ.eq Univ (join X X) X.
∀H8:∀X:Univ.eq Univ (meet X X) X.eq Univ (meet a (join b (meet a c))) (meet a (join b (meet c (join a (meet b c))))))
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
#H8 ##.
nauto by H0,H1,H2,H3,H4,H5,H6,H7,H8 ##;
ntry (nassumption) ##;
nqed.

(* ------------------------------------------------------------------------------ *)

include "logic/equality.ma".

(* Inclusion of: LAT163-1.p *)

(* ------------------------------------------------------------------------------ *)

(*  File     : LAT163-1 : TPTP v3.7.0. Released v3.1.0. *)

(*  Domain   : Lattice Theory *)

(*  Problem  : Huntington equation H76 implies H32 *)

(*  Version  : [McC05] (equality) axioms : Especial. *)

(*  English  :  *)

(*  Refs     : [McC05] McCune (2005), Email to Geoff Sutcliffe *)

(*  Source   : [McC05] *)

(*  Names    :  *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.89 v3.4.0, 0.88 v3.3.0, 0.93 v3.1.0 *)

(*  Syntax   : Number of clauses     :   10 (   0 non-Horn;  10 unit;   1 RR) *)

(*             Number of atoms       :   10 (  10 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    6 (   4 constant; 0-2 arity) *)

(*             Number of variables   :   20 (   2 singleton) *)

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
ntheorem prove_H32:
 (∀Univ:Type.∀U:Univ.∀X:Univ.∀Y:Univ.∀Z:Univ.
∀a:Univ.
∀b:Univ.
∀c:Univ.
∀d:Univ.
∀join:∀_:Univ.∀_:Univ.Univ.
∀meet:∀_:Univ.∀_:Univ.Univ.
∀H0:∀U:Univ.∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (meet X (join Y (meet Z (join Y U)))) (meet X (join Y (meet Z (join U (meet X Y))))).
∀H1:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (join (join X Y) Z) (join X (join Y Z)).
∀H2:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (meet (meet X Y) Z) (meet X (meet Y Z)).
∀H3:∀X:Univ.∀Y:Univ.eq Univ (join X Y) (join Y X).
∀H4:∀X:Univ.∀Y:Univ.eq Univ (meet X Y) (meet Y X).
∀H5:∀X:Univ.∀Y:Univ.eq Univ (join X (meet X Y)) X.
∀H6:∀X:Univ.∀Y:Univ.eq Univ (meet X (join X Y)) X.
∀H7:∀X:Univ.eq Univ (join X X) X.
∀H8:∀X:Univ.eq Univ (meet X X) X.eq Univ (meet a (join b (meet a (meet c d)))) (meet a (join b (meet c (join (meet a d) (meet b d))))))
.
#Univ ##.
#U ##.
#X ##.
#Y ##.
#Z ##.
#a ##.
#b ##.
#c ##.
#d ##.
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

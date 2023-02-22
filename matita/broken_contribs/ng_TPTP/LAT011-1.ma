include "logic/equality.ma".

(* Inclusion of: LAT011-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : LAT011-1 : TPTP v3.7.0. Released v2.2.0. *)

(*  Domain   : Lattice Theory *)

(*  Problem  : Uniqueness of meet (dually join) in lattice theory *)

(*  Version  : [MP96] (equality) axioms : Especial. *)

(*  English  : Let's say we have a lattice with two meet operations, say *)

(*             meet1 and meet2.  In other words, {join,meet1} is a lattice, *)

(*             and {join,meet2} is a lattice.  Then, we can prove that the *)

(*             two meet operations are really the same. *)

(*  Refs     : [McC98] McCune (1998), Email to G. Sutcliffe *)

(*           : [MP96]  McCune & Padmanabhan (1996), Automated Deduction in Eq *)

(*  Source   : [McC98] *)

(*  Names    : LT-8 [MP96] *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.00 v3.3.0, 0.07 v3.1.0, 0.00 v2.7.0, 0.09 v2.6.0, 0.00 v2.2.1 *)

(*  Syntax   : Number of clauses     :   14 (   0 non-Horn;  14 unit;   1 RR) *)

(*             Number of atoms       :   14 (  14 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    5 (   2 constant; 0-2 arity) *)

(*             Number of variables   :   26 (   4 singleton) *)

(*             Maximal term depth    :    3 (   2 average) *)

(*  Comments : For quasilattice, meet (dually join) is not necessarily unique. *)

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

(* ----{join,meet2} is a lattice: *)

(* ----Denial that meet1 and meet2 are the same: *)
ntheorem prove_meets_are_same:
 (∀Univ:Type.∀X:Univ.∀Y:Univ.∀Z:Univ.
∀a:Univ.
∀b:Univ.
∀join:∀_:Univ.∀_:Univ.Univ.
∀meet:∀_:Univ.∀_:Univ.Univ.
∀meet2:∀_:Univ.∀_:Univ.Univ.
∀H0:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (meet2 (meet2 X Y) Z) (meet2 X (meet2 Y Z)).
∀H1:∀X:Univ.∀Y:Univ.eq Univ (join X (meet2 X Y)) X.
∀H2:∀X:Univ.∀Y:Univ.eq Univ (meet2 X (join X Y)) X.
∀H3:∀X:Univ.∀Y:Univ.eq Univ (meet2 X Y) (meet2 Y X).
∀H4:∀X:Univ.eq Univ (meet2 X X) X.
∀H5:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (join (join X Y) Z) (join X (join Y Z)).
∀H6:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (meet (meet X Y) Z) (meet X (meet Y Z)).
∀H7:∀X:Univ.∀Y:Univ.eq Univ (join X Y) (join Y X).
∀H8:∀X:Univ.∀Y:Univ.eq Univ (meet X Y) (meet Y X).
∀H9:∀X:Univ.∀Y:Univ.eq Univ (join X (meet X Y)) X.
∀H10:∀X:Univ.∀Y:Univ.eq Univ (meet X (join X Y)) X.
∀H11:∀X:Univ.eq Univ (join X X) X.
∀H12:∀X:Univ.eq Univ (meet X X) X.eq Univ (meet a b) (meet2 a b))
.
#Univ ##.
#X ##.
#Y ##.
#Z ##.
#a ##.
#b ##.
#join ##.
#meet ##.
#meet2 ##.
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
#H12 ##.
nauto by H0,H1,H2,H3,H4,H5,H6,H7,H8,H9,H10,H11,H12 ##;
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)

include "logic/equality.ma".

(* Inclusion of: LAT024-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : LAT024-1 : TPTP v3.7.0. Released v2.2.0. *)

(*  Domain   : Lattice Theory (Quasilattices) *)

(*  Problem  : Meet (dually join) is not necessarily unique for quasilattices. *)

(*  Version  : [MP96] (equality) axioms. *)

(*  English  : Let's say we have a quasilattice with two meet operations, say *)

(*             meet1 and meet2.  In other words, {join,meet1} is a lattice, *)

(*             and {join,meet2} is a lattice.  Then, we can show that the *)

(*             two meet operations not necessarily the same. *)

(*  Refs     : [McC98] McCune (1998), Email to G. Sutcliffe *)

(*           : [MP96]  McCune & Padmanabhan (1996), Automated Deduction in Eq *)

(*  Source   : [McC98] *)

(*  Names    : QLT-7 [MP96] *)

(*  Status   : Satisfiable *)

(*  Rating   : 0.33 v3.2.0, 0.67 v3.1.0, 0.33 v2.4.0, 0.67 v2.3.0, 1.00 v2.2.1 *)

(*  Syntax   : Number of clauses     :   14 (   0 non-Horn;  14 unit;   1 RR) *)

(*             Number of atoms       :   14 (  14 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    5 (   2 constant; 0-2 arity) *)

(*             Number of variables   :   30 (   0 singleton) *)

(*             Maximal term depth    :    4 (   3 average) *)

(*  Comments : There is a 2-element model. *)

(*           : For lattices meet (dually join) is unique. *)

(* -------------------------------------------------------------------------- *)

(* ----Include Quasilattice theory (equality) axioms *)

(* Inclusion of: Axioms/LAT004-0.ax *)

(* -------------------------------------------------------------------------- *)

(*  File     : LAT004-0 : TPTP v3.7.0. Released v2.2.0. *)

(*  Domain   : Lattice Theory (Quasilattices) *)

(*  Axioms   : Quasilattice theory (equality) axioms *)

(*  Version  : [McC98b] (equality) axioms. *)

(*  English  :  *)

(*  Refs     : [McC98] McCune (1998), Email to G. Sutcliffe *)

(*           : [MP96]  McCune & Padmanabhan (1996), Automated Deduction in Eq *)

(*  Source   : [McC98] *)

(*  Names    :  *)

(*  Status   :  *)

(*  Syntax   : Number of clauses    :    8 (   0 non-Horn;   8 unit;   0 RR) *)

(*             Number of atoms      :    8 (   8 equality) *)

(*             Maximal clause size  :    1 (   1 average) *)

(*             Number of predicates :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors   :    2 (   0 constant; 2-2 arity) *)

(*             Number of variables  :   18 (   0 singleton) *)

(*             Maximal term depth   :    4 (   2 average) *)

(*  Comments :  *)

(* -------------------------------------------------------------------------- *)

(* ----Quasilattice theory: *)

(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)

(* ----{join,meet2} is a quasilattice: *)

(* ----Denial that meet1 and meet2 are the same: *)
ntheorem prove_meets_equal:
 (∀Univ:Type.∀X:Univ.∀Y:Univ.∀Z:Univ.
∀a:Univ.
∀b:Univ.
∀join:∀_:Univ.∀_:Univ.Univ.
∀meet:∀_:Univ.∀_:Univ.Univ.
∀meet2:∀_:Univ.∀_:Univ.Univ.
∀H0:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (meet2 (join X (meet2 Y Z)) (join X Y)) (join X (meet2 Y Z)).
∀H1:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (join (meet2 X (join Y Z)) (meet2 X Y)) (meet2 X (join Y Z)).
∀H2:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (meet2 (meet2 X Y) Z) (meet2 X (meet2 Y Z)).
∀H3:∀X:Univ.∀Y:Univ.eq Univ (meet2 X Y) (meet2 Y X).
∀H4:∀X:Univ.eq Univ (meet2 X X) X.
∀H5:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (meet (join X (meet Y Z)) (join X Y)) (join X (meet Y Z)).
∀H6:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (join (meet X (join Y Z)) (meet X Y)) (meet X (join Y Z)).
∀H7:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (join (join X Y) Z) (join X (join Y Z)).
∀H8:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (meet (meet X Y) Z) (meet X (meet Y Z)).
∀H9:∀X:Univ.∀Y:Univ.eq Univ (join X Y) (join Y X).
∀H10:∀X:Univ.∀Y:Univ.eq Univ (meet X Y) (meet Y X).
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

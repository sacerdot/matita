include "logic/equality.ma".

(* Inclusion of: LAT021-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : LAT021-1 : TPTP v3.7.0. Released v2.2.0. *)

(*  Domain   : Lattice Theory (Quasilattices) *)

(*  Problem  : Bowden's inequality gives distributivity in lattice theory. *)

(*  Version  : [MP96] (equality) axioms. *)

(*  English  :  *)

(*  Refs     : [McC98] McCune (1998), Email to G. Sutcliffe *)

(*           : [MP96]  McCune & Padmanabhan (1996), Automated Deduction in Eq *)

(*  Source   : [McC98] *)

(*  Names    : QLT-4 [MP96] *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.11 v3.4.0, 0.12 v3.3.0, 0.00 v2.5.0, 0.25 v2.4.0, 0.00 v2.2.1 *)

(*  Syntax   : Number of clauses     :   10 (   0 non-Horn;  10 unit;   1 RR) *)

(*             Number of atoms       :   10 (  10 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    5 (   3 constant; 0-2 arity) *)

(*             Number of variables   :   21 (   0 singleton) *)

(*             Maximal term depth    :    4 (   3 average) *)

(*  Comments : Bowden's inequality is written as an equation. *)

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

(* ----Bowden's inequality (as an equation): *)

(* ----Denial of distributivity: *)
ntheorem prove_distributivity:
 (∀Univ:Type.∀X:Univ.∀Y:Univ.∀Z:Univ.
∀a:Univ.
∀b:Univ.
∀c:Univ.
∀join:∀_:Univ.∀_:Univ.Univ.
∀meet:∀_:Univ.∀_:Univ.Univ.
∀H0:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (join (join X (meet Y Z)) (meet (join X Y) Z)) (join X (meet Y Z)).
∀H1:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (meet (join X (meet Y Z)) (join X Y)) (join X (meet Y Z)).
∀H2:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (join (meet X (join Y Z)) (meet X Y)) (meet X (join Y Z)).
∀H3:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (join (join X Y) Z) (join X (join Y Z)).
∀H4:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (meet (meet X Y) Z) (meet X (meet Y Z)).
∀H5:∀X:Univ.∀Y:Univ.eq Univ (join X Y) (join Y X).
∀H6:∀X:Univ.∀Y:Univ.eq Univ (meet X Y) (meet Y X).
∀H7:∀X:Univ.eq Univ (join X X) X.
∀H8:∀X:Univ.eq Univ (meet X X) X.eq Univ (meet a (join b c)) (join (meet a b) (meet a c)))
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

(* -------------------------------------------------------------------------- *)

include "logic/equality.ma".

(* Inclusion of: LAT028-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : LAT028-1 : TPTP v3.7.0. Released v2.2.0. *)

(*  Domain   : Lattice Theory (Weakly Associative Lattices) *)

(*  Problem  : Uniqueness of meet (dually join) in WAL *)

(*  Version  : [MP96] (equality) axioms. *)

(*  English  : Let's say we have a weakly-associative lattice (WAL) with 2 meet *)

(*             operations, say meet1 and meet2.  In other words, {join,meet1} *)

(*             is a WAL, and {join,meet2} is a WAL.  Then, we can prove that the *)

(*             two meet operations are really the same. *)

(*  Refs     : [McC98] McCune (1998), Email to G. Sutcliffe *)

(*           : [MP96]  McCune & Padmanabhan (1996), Automated Deduction in Eq *)

(*  Source   : [McC98] *)

(*  Names    : WAL-2 [MP96] *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.00 v2.2.1 *)

(*  Syntax   : Number of clauses     :   11 (   0 non-Horn;  11 unit;   1 RR) *)

(*             Number of atoms       :   11 (  11 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    5 (   2 constant; 0-2 arity) *)

(*             Number of variables   :   21 (   8 singleton) *)

(*             Maximal term depth    :    4 (   2 average) *)

(*  Comments : *)

(* -------------------------------------------------------------------------- *)

(* ----Include Weakly Associative Lattices theory (equality) axioms *)

(* Inclusion of: Axioms/LAT005-0.ax *)

(* ------------------------------------------------------------------------------ *)

(*  File     : LAT005-0 : TPTP v3.7.0. Released v2.2.0. *)

(*  Domain   : Lattice Theory (Weakly Associative Lattices) *)

(*  Axioms   : Weakly Associative Lattices theory (equality) axioms *)

(*  Version  : [McC98b] (equality) axioms. *)

(*  English  :  *)

(*  Refs     : [McC98] McCune (1998), Email to G. Sutcliffe *)

(*           : [MP96]  McCune & Padmanabhan (1996), Automated Deduction in Eq *)

(*  Source   : [McC98] *)

(*  Names    :  *)

(*  Status   :  *)

(*  Syntax   : Number of clauses    :    6 (   0 non-Horn;   6 unit;   0 RR) *)

(*             Number of atoms      :    6 (   6 equality) *)

(*             Maximal clause size  :    1 (   1 average) *)

(*             Number of predicates :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors   :    2 (   0 constant; 2-2 arity) *)

(*             Number of variables  :   12 (   4 singleton) *)

(*             Maximal term depth   :    4 (   2 average) *)

(*  Comments :  *)

(* ------------------------------------------------------------------------------ *)

(* ----Axioms for a weakly associative lattice: *)

(* ------------------------------------------------------------------------------ *)

(* -------------------------------------------------------------------------- *)

(* ----{join,meet2} is a weakly-associative lattice: *)

(* ----Denial of meet=meet2: *)
ntheorem name:
 (∀Univ:Type.∀X:Univ.∀Y:Univ.∀Z:Univ.
∀a:Univ.
∀b:Univ.
∀join:∀_:Univ.∀_:Univ.Univ.
∀meet:∀_:Univ.∀_:Univ.Univ.
∀meet2:∀_:Univ.∀_:Univ.Univ.
∀H0:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (join (join (meet2 X Y) (meet2 Z Y)) Y) Y.
∀H1:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (meet2 (meet2 (join X Y) (join Z Y)) Y) Y.
∀H2:∀X:Univ.∀Y:Univ.eq Univ (meet2 X Y) (meet2 Y X).
∀H3:∀X:Univ.eq Univ (meet2 X X) X.
∀H4:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (join (join (meet X Y) (meet Z Y)) Y) Y.
∀H5:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (meet (meet (join X Y) (join Z Y)) Y) Y.
∀H6:∀X:Univ.∀Y:Univ.eq Univ (join X Y) (join Y X).
∀H7:∀X:Univ.∀Y:Univ.eq Univ (meet X Y) (meet Y X).
∀H8:∀X:Univ.eq Univ (join X X) X.
∀H9:∀X:Univ.eq Univ (meet X X) X.eq Univ (meet a b) (meet2 a b))
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
nauto by H0,H1,H2,H3,H4,H5,H6,H7,H8,H9 ##;
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)

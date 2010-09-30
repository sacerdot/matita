include "logic/equality.ma".

(* Inclusion of: LAT026-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : LAT026-1 : TPTP v3.7.0. Released v2.2.0. *)

(*  Domain   : Lattice Theory (Weakly Associative Lattices) *)

(*  Problem  : WAL + absorption gives LT, part 1. *)

(*  Version  : [MP96] (equality) axioms. *)

(*  English  : A Weakly associative lattice (WAL) satisfying an absorption *)

(*             law is associative, and therefore a full lattice, part 1. *)

(*  Refs     : [McC98] McCune (1998), Email to G. Sutcliffe *)

(*           : [MP96]  McCune & Padmanabhan (1996), Automated Deduction in Eq *)

(*  Source   : [McC98] *)

(*  Names    : WAL-1-a [MP96] *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.00 v3.3.0, 0.14 v3.1.0, 0.11 v2.7.0, 0.09 v2.6.0, 0.00 v2.4.0, 0.00 v2.2.1 *)

(*  Syntax   : Number of clauses     :    8 (   0 non-Horn;   8 unit;   1 RR) *)

(*             Number of atoms       :    8 (   8 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    5 (   3 constant; 0-2 arity) *)

(*             Number of variables   :   15 (   6 singleton) *)

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

(* ----An absorption law. *)

(* ----Denial of associativity of meet: *)
ntheorem prove_associativity_of_meet:
 (∀Univ:Type.∀X:Univ.∀Y:Univ.∀Z:Univ.
∀a:Univ.
∀b:Univ.
∀c:Univ.
∀join:∀_:Univ.∀_:Univ.Univ.
∀meet:∀_:Univ.∀_:Univ.Univ.
∀H0:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (meet X (join Y (join X Z))) X.
∀H1:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (join (join (meet X Y) (meet Z Y)) Y) Y.
∀H2:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (meet (meet (join X Y) (join Z Y)) Y) Y.
∀H3:∀X:Univ.∀Y:Univ.eq Univ (join X Y) (join Y X).
∀H4:∀X:Univ.∀Y:Univ.eq Univ (meet X Y) (meet Y X).
∀H5:∀X:Univ.eq Univ (join X X) X.
∀H6:∀X:Univ.eq Univ (meet X X) X.eq Univ (meet (meet a b) c) (meet a (meet b c)))
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
nauto by H0,H1,H2,H3,H4,H5,H6 ##;
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)

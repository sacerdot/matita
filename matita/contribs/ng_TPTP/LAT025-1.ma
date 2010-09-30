include "logic/equality.ma".

(* Inclusion of: LAT025-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : LAT025-1 : TPTP v3.7.0. Released v2.2.0. *)

(*  Domain   : Lattice Theory (Ternary Near Lattices) *)

(*  Problem  : Non-uniqueness of meet (dually join) in TNL *)

(*  Version  : [MP96] (equality) axioms. *)

(*  English  : Let's say we have a ternary near-lattice (TNL) with two meet *)

(*             operations, say meet1 and meet2.  In other words, {join,meet1} *)

(*             and {join,meet2} are TNLs.  Are the two meets necessarily *)

(*             the same?  No, they aren't.  Here is a counterexample. *)

(*  Refs     : [McC98] McCune (1998), Email to G. Sutcliffe *)

(*           : [MP96]  McCune & Padmanabhan (1996), Automated Deduction in Eq *)

(*  Source   : [McC98] *)

(*  Names    : TNL-2 [MP96] *)

(*  Status   : Satisfiable *)

(*  Rating   : 0.33 v3.2.0, 0.67 v3.1.0, 0.33 v2.4.0, 0.67 v2.3.0, 1.00 v2.2.1 *)

(*  Syntax   : Number of clauses     :   15 (   0 non-Horn;  15 unit;   1 RR) *)

(*             Number of atoms       :   15 (  15 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    5 (   2 constant; 0-2 arity) *)

(*             Number of variables   :   29 (  12 singleton) *)

(*             Maximal term depth    :    4 (   2 average) *)

(*  Comments : The smallest model has 5 elements. *)

(* -------------------------------------------------------------------------- *)

(* ----{join,meet} is a TNL: *)

(* ----{join,meet2} is a TNL: *)

(* ----Denial of meet=meet2. *)
ntheorem prove_meets_equal:
 (∀Univ:Type.∀X:Univ.∀Y:Univ.∀Z:Univ.
∀a:Univ.
∀b:Univ.
∀join:∀_:Univ.∀_:Univ.Univ.
∀meet:∀_:Univ.∀_:Univ.Univ.
∀meet2:∀_:Univ.∀_:Univ.Univ.
∀H0:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (meet2 X (join Y (join X Z))) X.
∀H1:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (join X (meet2 Y (meet2 X Z))) X.
∀H2:∀X:Univ.∀Y:Univ.eq Univ (meet2 X Y) (meet2 Y X).
∀H3:∀X:Univ.∀Y:Univ.eq Univ (join X (meet2 X Y)) X.
∀H4:∀X:Univ.∀Y:Univ.eq Univ (meet2 X (join X Y)) X.
∀H5:∀X:Univ.eq Univ (meet2 X X) X.
∀H6:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (meet X (join Y (join X Z))) X.
∀H7:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (join X (meet Y (meet X Z))) X.
∀H8:∀X:Univ.∀Y:Univ.eq Univ (join X Y) (join Y X).
∀H9:∀X:Univ.∀Y:Univ.eq Univ (meet X Y) (meet Y X).
∀H10:∀X:Univ.∀Y:Univ.eq Univ (join X (meet X Y)) X.
∀H11:∀X:Univ.∀Y:Univ.eq Univ (meet X (join X Y)) X.
∀H12:∀X:Univ.eq Univ (join X X) X.
∀H13:∀X:Univ.eq Univ (meet X X) X.eq Univ (meet a b) (meet2 a b))
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
#H13 ##.
nauto by H0,H1,H2,H3,H4,H5,H6,H7,H8,H9,H10,H11,H12,H13 ##;
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)

include "logic/equality.ma".

(* Inclusion of: LAT007-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : LAT007-1 : TPTP v3.7.0. Released v2.2.0. *)

(*  Domain   : Lattice Theory (Distributive lattices) *)

(*  Problem  : Sholander's basis for distributive lattices, part 5 (of 6). *)

(*  Version  : [MP96] (equality) axioms. *)

(*  English  : This is part of the proof that Sholanders 2-basis for *)

(*             distributive lattices is correct. Here we prove associativity  *)

(*             of join. *)

(*  Refs     : [McC98] McCune (1998), Email to G. Sutcliffe *)

(*           : [MP96]  McCune & Padmanabhan (1996), Automated Deduction in Eq *)

(*  Source   : [McC98] *)

(*  Names    : LT-3-e [MP96] *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.33 v3.4.0, 0.38 v3.3.0, 0.36 v3.1.0, 0.33 v2.7.0, 0.27 v2.6.0, 0.17 v2.5.0, 0.00 v2.2.1 *)

(*  Syntax   : Number of clauses     :    3 (   0 non-Horn;   3 unit;   1 RR) *)

(*             Number of atoms       :    3 (   3 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    5 (   3 constant; 0-2 arity) *)

(*             Number of variables   :    5 (   1 singleton) *)

(*             Maximal term depth    :    3 (   3 average) *)

(*  Comments : *)

(* -------------------------------------------------------------------------- *)

(* ----Sholander's 2-basis for distributive lattices: *)

(* ----Denial of the conclusion: *)
ntheorem prove_associativity_of_join:
 (∀Univ:Type.∀X:Univ.∀Y:Univ.∀Z:Univ.
∀a:Univ.
∀b:Univ.
∀c:Univ.
∀join:∀_:Univ.∀_:Univ.Univ.
∀meet:∀_:Univ.∀_:Univ.Univ.
∀H0:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (meet X (join Y Z)) (join (meet Z X) (meet Y X)).
∀H1:∀X:Univ.∀Y:Univ.eq Univ (meet X (join X Y)) X.eq Univ (join (join a b) c) (join a (join b c)))
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
nauto by H0,H1 ##;
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)

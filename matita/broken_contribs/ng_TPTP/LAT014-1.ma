include "logic/equality.ma".

(* Inclusion of: LAT014-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : LAT014-1 : TPTP v3.7.0. Released v2.2.0. *)

(*  Domain   : Lattice Theory *)

(*  Problem  : McKenzie's 4-basis for lattice theory, part 3 (of 3) *)

(*  Version  : [MP96] (equality) axioms. *)

(*  English  : This is part of a proof that McKenzie's 4-basis axiomatizes *)

(*             lattice theory.  We prove half of the standard basis. *)

(*             The other half follows by duality. In this part we prove *)

(*             absorbtion of meet. *)

(*  Refs     : [McC98] McCune (1998), Email to G. Sutcliffe *)

(*           : [MP96]  McCune & Padmanabhan (1996), Automated Deduction in Eq *)

(*  Source   : [McC98] *)

(*  Names    : LT-9 [MP96] *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.00 v2.2.1 *)

(*  Syntax   : Number of clauses     :    5 (   0 non-Horn;   5 unit;   1 RR) *)

(*             Number of atoms       :    5 (   5 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    4 (   2 constant; 0-2 arity) *)

(*             Number of variables   :   12 (   8 singleton) *)

(*             Maximal term depth    :    4 (   2 average) *)

(*  Comments : *)

(* -------------------------------------------------------------------------- *)

(* ----McKenzie's self-dual (independent) absorptive 4-basis for lattice theory. *)

(* ----Denial of conclusion: *)
ntheorem prove_absorbtion:
 (∀Univ:Type.∀X:Univ.∀Y:Univ.∀Z:Univ.
∀a:Univ.
∀b:Univ.
∀join:∀_:Univ.∀_:Univ.Univ.
∀meet:∀_:Univ.∀_:Univ.Univ.
∀H0:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (meet (meet (join X Y) (join Y Z)) Y) Y.
∀H1:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (join (join (meet X Y) (meet Y Z)) Y) Y.
∀H2:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (meet X (join Y (join X Z))) X.
∀H3:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (join X (meet Y (meet X Z))) X.eq Univ (meet a (join a b)) a)
.
#Univ ##.
#X ##.
#Y ##.
#Z ##.
#a ##.
#b ##.
#join ##.
#meet ##.
#H0 ##.
#H1 ##.
#H2 ##.
#H3 ##.
nauto by H0,H1,H2,H3 ##;
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)

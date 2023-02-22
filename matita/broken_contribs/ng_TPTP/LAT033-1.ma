include "logic/equality.ma".

(* Inclusion of: LAT033-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : LAT033-1 : TPTP v3.7.0. Bugfixed v2.5.0. *)

(*  Domain   : Lattice Theory *)

(*  Problem  : Idempotency of join *)

(*  Version  : [McC88] (equality) axioms. *)

(*  English  : *)

(*  Refs     : [DeN00] DeNivelle (2000), Email to G. Sutcliffe *)

(*             [McC88] McCune (1988), Challenge Equality Problems in Lattice *)

(*  Source   : [DeN00] *)

(*  Names    : idemp_of_join [DeN00] *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.00 v2.5.0 *)

(*  Syntax   : Number of clauses     :    7 (   0 non-Horn;   7 unit;   1 RR) *)

(*             Number of atoms       :    7 (   7 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    3 (   1 constant; 0-2 arity) *)

(*             Number of variables   :   14 (   2 singleton) *)

(*             Maximal term depth    :    3 (   2 average) *)

(*  Comments :  *)

(*  Bugfixes : v2.5.0 - Used axioms without the conjecture *)

(* -------------------------------------------------------------------------- *)

(* ----Include lattice theory axioms *)

(* include('Axioms/LAT001-0.ax'). *)

(* -------------------------------------------------------------------------- *)
ntheorem idempotence_of_join:
 (∀Univ:Type.∀X:Univ.∀Y:Univ.∀Z:Univ.
∀join:∀_:Univ.∀_:Univ.Univ.
∀meet:∀_:Univ.∀_:Univ.Univ.
∀xx:Univ.
∀H0:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (join (join X Y) Z) (join X (join Y Z)).
∀H1:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (meet (meet X Y) Z) (meet X (meet Y Z)).
∀H2:∀X:Univ.∀Y:Univ.eq Univ (join X Y) (join Y X).
∀H3:∀X:Univ.∀Y:Univ.eq Univ (meet X Y) (meet Y X).
∀H4:∀X:Univ.∀Y:Univ.eq Univ (join X (meet X Y)) X.
∀H5:∀X:Univ.∀Y:Univ.eq Univ (meet X (join X Y)) X.eq Univ (join xx xx) xx)
.
#Univ ##.
#X ##.
#Y ##.
#Z ##.
#join ##.
#meet ##.
#xx ##.
#H0 ##.
#H1 ##.
#H2 ##.
#H3 ##.
#H4 ##.
#H5 ##.
nauto by H0,H1,H2,H3,H4,H5 ##;
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)

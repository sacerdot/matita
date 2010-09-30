include "logic/equality.ma".

(* Inclusion of: LAT038-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : LAT038-1 : TPTP v3.7.0. Released v2.4.0. *)

(*  Domain   : Lattice Theory *)

(*  Problem  : Simplification rule in a distributive lattice *)

(*  Version  : [McC88] (equality) axioms. *)

(*  English  : In a distributive lattice, the following simplification rule  *)

(*             holds: *)

(*             forall a, b, c, d:  *)

(*                 if   f(a v b, d) = f(c v b, d) and *)

(*                      f(a, d) & f(b, d) = f(c, d) & f(b, d) *)

(*                 then f(a,d) = f(c,d). *)

(*  Refs     : [DeN00] DeNivelle (2000), Email to G. Sutcliffe *)

(*             [McC88] McCune (1988), Challenge Equality Problems in Lattice *)

(*  Source   : [DeN00] *)

(*  Names    : lattice-hemi-simplif [DeN00] *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.11 v3.4.0, 0.12 v3.3.0, 0.43 v3.1.0, 0.44 v2.7.0, 0.36 v2.6.0, 0.17 v2.5.0, 0.25 v2.4.0 *)

(*  Syntax   : Number of clauses     :   17 (   0 non-Horn;  17 unit;   3 RR) *)

(*             Number of atoms       :   17 (  17 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    8 (   5 constant; 0-2 arity) *)

(*             Number of variables   :   30 (   4 singleton) *)

(*             Maximal term depth    :    3 (   2 average) *)

(*  Comments :  *)

(* -------------------------------------------------------------------------- *)

(* ----Include lattice theory axioms *)

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
ntheorem rhs:
 (∀Univ:Type.∀U:Univ.∀V:Univ.∀W:Univ.∀X:Univ.∀Y:Univ.∀Z:Univ.
∀aa:Univ.
∀bb:Univ.
∀cc:Univ.
∀dd:Univ.
∀f:∀_:Univ.∀_:Univ.Univ.
∀join:∀_:Univ.∀_:Univ.Univ.
∀meet:∀_:Univ.∀_:Univ.Univ.
∀n0:Univ.
∀H0:eq Univ (meet (f aa dd) (f bb dd)) (meet (f cc dd) (f bb dd)).
∀H1:eq Univ (f (join aa bb) dd) (f (join cc bb) dd).
∀H2:∀W:Univ.eq Univ (f W n0) n0.
∀H3:∀U:Univ.∀V:Univ.∀W:Univ.eq Univ (f W (join U V)) (join (f W U) (f W V)).
∀H4:∀W:Univ.eq Univ (f n0 W) n0.
∀H5:∀U:Univ.∀V:Univ.∀W:Univ.eq Univ (f (join U V) W) (join (f U W) (f V W)).
∀H6:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (meet X (join Y Z)) (join (meet X Y) (meet X Z)).
∀H7:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (join X (meet Y Z)) (meet (join X Y) (join X Z)).
∀H8:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (join (join X Y) Z) (join X (join Y Z)).
∀H9:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (meet (meet X Y) Z) (meet X (meet Y Z)).
∀H10:∀X:Univ.∀Y:Univ.eq Univ (join X Y) (join Y X).
∀H11:∀X:Univ.∀Y:Univ.eq Univ (meet X Y) (meet Y X).
∀H12:∀X:Univ.∀Y:Univ.eq Univ (join X (meet X Y)) X.
∀H13:∀X:Univ.∀Y:Univ.eq Univ (meet X (join X Y)) X.
∀H14:∀X:Univ.eq Univ (join X X) X.
∀H15:∀X:Univ.eq Univ (meet X X) X.eq Univ (f aa dd) (f cc dd))
.
#Univ ##.
#U ##.
#V ##.
#W ##.
#X ##.
#Y ##.
#Z ##.
#aa ##.
#bb ##.
#cc ##.
#dd ##.
#f ##.
#join ##.
#meet ##.
#n0 ##.
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
#H14 ##.
#H15 ##.
nauto by H0,H1,H2,H3,H4,H5,H6,H7,H8,H9,H10,H11,H12,H13,H14,H15 ##;
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)

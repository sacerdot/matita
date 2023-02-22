include "logic/equality.ma".

(* Inclusion of: COL042-9.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : COL042-9 : TPTP v3.7.0. Released v2.1.0. *)

(*  Domain   : Combinatory Logic *)

(*  Problem  : Strong fixed point for B and W1 *)

(*  Version  : [WM88] (equality) axioms. *)

(*             Theorem formulation : The fixed point is provided and checked. *)

(*  English  : The strong fixed point property holds for the set  *)

(*             P consisting of the combinators B and W1, where ((Bx)y)z  *)

(*             = x(yz), (W1x)y = (yx)x. *)

(*  Refs     : [WM88]  Wos & McCune (1988), Challenge Problems Focusing on Eq *)

(*           : [Wos93] Wos (1993), The Kernel Strategy and Its Use for the St *)

(*  Source   : [TPTP] *)

(*  Names    :  *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.11 v3.4.0, 0.12 v3.3.0, 0.14 v3.1.0, 0.11 v2.7.0, 0.18 v2.6.0, 0.00 v2.5.0, 0.25 v2.4.0, 0.00 v2.2.1, 0.38 v2.2.0, 0.60 v2.1.0 *)

(*  Syntax   : Number of clauses     :    4 (   0 non-Horn;   4 unit;   2 RR) *)

(*             Number of atoms       :    4 (   4 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    5 (   4 constant; 0-2 arity) *)

(*             Number of variables   :    5 (   0 singleton) *)

(*             Maximal term depth    :    5 (   3 average) *)

(*  Comments :  *)

(* -------------------------------------------------------------------------- *)
ntheorem prove_strong_fixed_point:
 (∀Univ:Type.∀X:Univ.∀Y:Univ.∀Z:Univ.
∀apply:∀_:Univ.∀_:Univ.Univ.
∀b:Univ.
∀fixed_pt:Univ.
∀strong_fixed_point:Univ.
∀w1:Univ.
∀H0:eq Univ strong_fixed_point (apply (apply b (apply w1 w1)) (apply (apply b (apply b w1)) (apply (apply b b) b))).
∀H1:∀X:Univ.∀Y:Univ.eq Univ (apply (apply w1 X) Y) (apply (apply Y X) X).
∀H2:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (apply (apply (apply b X) Y) Z) (apply X (apply Y Z)).eq Univ (apply strong_fixed_point fixed_pt) (apply fixed_pt (apply strong_fixed_point fixed_pt)))
.
#Univ ##.
#X ##.
#Y ##.
#Z ##.
#apply ##.
#b ##.
#fixed_pt ##.
#strong_fixed_point ##.
#w1 ##.
#H0 ##.
#H1 ##.
#H2 ##.
nauto by H0,H1,H2 ##;
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)

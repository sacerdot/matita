include "logic/equality.ma".

(* Inclusion of: COL066-2.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : COL066-2 : TPTP v3.7.0. Bugfixed v1.2.0. *)

(*  Domain   : Combinatory Logic *)

(*  Problem  : Find combinator equivalent to P from B, Q and W *)

(*  Version  : [WM88] (equality) axioms. *)

(*             Theorem formulation : The combinator is provided and checked. *)

(*  English  : Construct from B, Q and W alone a combinator that behaves as *)

(*             the combinator P does, where ((Bx)y)z = x(yz), ((Qx)y)z = *)

(*             y(xz), (Wx)y = (xy)y, (((Px)y)y)z = (xy)((xy)z) *)

(*  Refs     : [WM88]  Wos & McCune (1988), Challenge Problems Focusing on Eq *)

(*           : [WW+90] Wos et al. (1990), Automated Reasoning Contributes to  *)

(*  Source   : [TPTP] *)

(*  Names    :  *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.11 v3.4.0, 0.12 v3.3.0, 0.00 v2.7.0, 0.09 v2.6.0, 0.00 v2.1.0, 0.29 v2.0.0 *)

(*  Syntax   : Number of clauses     :    4 (   0 non-Horn;   4 unit;   1 RR) *)

(*             Number of atoms       :    4 (   4 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    7 (   6 constant; 0-2 arity) *)

(*             Number of variables   :    8 (   0 singleton) *)

(*             Maximal term depth    :    9 (   4 average) *)

(*  Comments :  *)

(*  Bugfixes : v1.2.0 : Redundant [fgh]_substitution axioms removed. *)

(* -------------------------------------------------------------------------- *)

(* ----This is the P equivalent *)
ntheorem prove_p_combinator:
 (∀Univ:Type.∀X:Univ.∀Y:Univ.∀Z:Univ.
∀apply:∀_:Univ.∀_:Univ.Univ.
∀b:Univ.
∀q:Univ.
∀w:Univ.
∀x:Univ.
∀y:Univ.
∀z:Univ.
∀H0:∀X:Univ.∀Y:Univ.eq Univ (apply (apply w X) Y) (apply (apply X Y) Y).
∀H1:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (apply (apply (apply q X) Y) Z) (apply Y (apply X Z)).
∀H2:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (apply (apply (apply b X) Y) Z) (apply X (apply Y Z)).eq Univ (apply (apply (apply (apply (apply (apply q q) (apply w (apply q (apply q q)))) x) y) y) z) (apply (apply x y) (apply (apply x y) z)))
.
#Univ ##.
#X ##.
#Y ##.
#Z ##.
#apply ##.
#b ##.
#q ##.
#w ##.
#x ##.
#y ##.
#z ##.
#H0 ##.
#H1 ##.
#H2 ##.
nauto by H0,H1,H2 ##;
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)

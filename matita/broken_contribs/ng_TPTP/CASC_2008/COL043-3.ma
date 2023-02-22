include "logic/equality.ma".

(* Inclusion of: COL043-3.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : COL043-3 : TPTP v3.7.0. Bugfixed v2.3.0. *)

(*  Domain   : Combinatory Logic *)

(*  Problem  : Strong fixed point for B and H *)

(*  Version  : [WM88] (equality) axioms. *)

(*             Theorem formulation : The fixed point is provided and checked. *)

(*  English  : The strong fixed point property holds for the set  *)

(*             P consisting of the combinators B and H, where ((Bx)y)z  *)

(*             = x(yz), ((Hx)y)z = ((xy)z)y. *)

(*  Refs     : [WM88]  Wos & McCune (1988), Challenge Problems Focusing on Eq *)

(*           : [Wos93] Wos (1993), The Kernel Strategy and Its Use for the St *)

(*  Source   : [TPTP] *)

(*  Names    : - [Wos93] *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.67 v3.4.0, 0.75 v3.3.0, 0.79 v3.2.0, 0.71 v3.1.0, 0.78 v2.7.0, 1.00 v2.6.0, 0.83 v2.5.0, 0.75 v2.4.0, 0.67 v2.3.0 *)

(*  Syntax   : Number of clauses     :    4 (   0 non-Horn;   4 unit;   2 RR) *)

(*             Number of atoms       :    4 (   4 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    5 (   4 constant; 0-2 arity) *)

(*             Number of variables   :    6 (   0 singleton) *)

(*             Maximal term depth    :   11 (   4 average) *)

(*  Comments :  *)

(*  Bugfixes : v2.3.0 - Clause strong_fixed_point fixed. *)

(* -------------------------------------------------------------------------- *)
ntheorem prove_strong_fixed_point:
 (∀Univ:Type.∀X:Univ.∀Y:Univ.∀Z:Univ.
∀apply:∀_:Univ.∀_:Univ.Univ.
∀b:Univ.
∀fixed_pt:Univ.
∀h:Univ.
∀strong_fixed_point:Univ.
∀H0:eq Univ strong_fixed_point (apply (apply b (apply (apply b (apply (apply h (apply (apply b (apply (apply b h) (apply b b))) (apply h (apply (apply b h) (apply b b))))) h)) b)) b).
∀H1:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (apply (apply (apply h X) Y) Z) (apply (apply (apply X Y) Z) Y).
∀H2:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (apply (apply (apply b X) Y) Z) (apply X (apply Y Z)).eq Univ (apply strong_fixed_point fixed_pt) (apply fixed_pt (apply strong_fixed_point fixed_pt)))
.
#Univ ##.
#X ##.
#Y ##.
#Z ##.
#apply ##.
#b ##.
#fixed_pt ##.
#h ##.
#strong_fixed_point ##.
#H0 ##.
#H1 ##.
#H2 ##.
nauto by H0,H1,H2 ##;
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)

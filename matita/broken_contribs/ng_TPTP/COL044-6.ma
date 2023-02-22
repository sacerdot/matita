include "logic/equality.ma".

(* Inclusion of: COL044-6.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : COL044-6 : TPTP v3.7.0. Released v2.1.0. *)

(*  Domain   : Combinatory Logic *)

(*  Problem  : Strong fixed point for B and N *)

(*  Version  : [WM88] (equality) axioms. *)

(*             Theorem formulation : The fixed point is provided and checked. *)

(*  English  : The strong fixed point property holds for the set  *)

(*             P consisting of the combinators B and N, where ((Bx)y)z  *)

(*             = x(yz), ((Nx)y)z = ((xz)y)z. *)

(*  Refs     : [WM88]  Wos & McCune (1988), Challenge Problems Focusing on Eq *)

(*           : [Wos93] Wos (1993), The Kernel Strategy and Its Use for the St *)

(*  Source   : [TPTP] *)

(*  Names    :  *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.56 v3.4.0, 0.62 v3.3.0, 0.71 v3.2.0, 0.64 v3.1.0, 0.56 v2.7.0, 0.82 v2.6.0, 0.67 v2.5.0, 0.50 v2.4.0, 0.67 v2.2.1, 0.88 v2.2.0, 0.80 v2.1.0 *)

(*  Syntax   : Number of clauses     :    4 (   0 non-Horn;   4 unit;   2 RR) *)

(*             Number of atoms       :    4 (   4 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    5 (   4 constant; 0-2 arity) *)

(*             Number of variables   :    6 (   0 singleton) *)

(*             Maximal term depth    :   12 (   4 average) *)

(*  Comments :  *)

(* -------------------------------------------------------------------------- *)
ntheorem prove_strong_fixed_point:
 (∀Univ:Type.∀X:Univ.∀Y:Univ.∀Z:Univ.
∀apply:∀_:Univ.∀_:Univ.Univ.
∀b:Univ.
∀fixed_pt:Univ.
∀n:Univ.
∀strong_fixed_point:Univ.
∀H0:eq Univ strong_fixed_point (apply (apply b (apply (apply b (apply (apply n (apply (apply b b) (apply (apply n (apply (apply b b) n)) n))) n)) b)) b).
∀H1:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (apply (apply (apply n X) Y) Z) (apply (apply (apply X Z) Y) Z).
∀H2:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (apply (apply (apply b X) Y) Z) (apply X (apply Y Z)).eq Univ (apply strong_fixed_point fixed_pt) (apply fixed_pt (apply strong_fixed_point fixed_pt)))
.
#Univ ##.
#X ##.
#Y ##.
#Z ##.
#apply ##.
#b ##.
#fixed_pt ##.
#n ##.
#strong_fixed_point ##.
#H0 ##.
#H1 ##.
#H2 ##.
nauto by H0,H1,H2 ##;
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)

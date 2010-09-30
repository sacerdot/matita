include "logic/equality.ma".

(* Inclusion of: COL002-4.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : COL002-4 : TPTP v3.7.0. Bugfixed v3.1.0. *)

(*  Domain   : Combinatory Logic *)

(*  Problem  : Weak fixed point for S, B, C, and I *)

(*  Version  : [WM88] (equality) axioms. *)

(*             Theorem formulation : The fixed point is provided and checked. *)

(*  English  : The weak fixed point property holds for the set P consisting  *)

(*             of the combinators S, B, C, and I, where ((Sx)y)z = (xz)(yz),  *)

(*             ((Bx)y)z = x(yz), ((Cx)y)z = (xz)y, and Ix = x. *)

(*  Refs     : [WM88]  Wos & McCune (1988), Challenge Problems Focusing on Eq *)

(*  Source   : [TPTP] *)

(*  Names    :  *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.11 v3.4.0, 0.12 v3.3.0, 0.07 v3.1.0 *)

(*  Syntax   : Number of clauses     :    6 (   0 non-Horn;   6 unit;   1 RR) *)

(*             Number of atoms       :    6 (   6 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    7 (   5 constant; 0-2 arity) *)

(*             Number of variables   :   11 (   0 singleton) *)

(*             Maximal term depth    :    5 (   3 average) *)

(*  Comments : This is the one found in proofs 1 and 2 of C1.1 in [WM88]. *)

(*  Bugfixes : Fixed clauses weak_fixed_point and prove_weak_fixed_point. *)

(* -------------------------------------------------------------------------- *)
ntheorem prove_weak_fixed_point:
 (∀Univ:Type.∀X:Univ.∀Y:Univ.∀Z:Univ.
∀apply:∀_:Univ.∀_:Univ.Univ.
∀b:Univ.
∀c:Univ.
∀fixed_pt:Univ.
∀i:Univ.
∀s:Univ.
∀weak_fixed_point:∀_:Univ.Univ.
∀H0:∀X:Univ.eq Univ (weak_fixed_point X) (apply (apply (apply s (apply b X)) i) (apply (apply s (apply b X)) i)).
∀H1:∀X:Univ.eq Univ (apply i X) X.
∀H2:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (apply (apply (apply c X) Y) Z) (apply (apply X Z) Y).
∀H3:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (apply (apply (apply b X) Y) Z) (apply X (apply Y Z)).
∀H4:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (apply (apply (apply s X) Y) Z) (apply (apply X Z) (apply Y Z)).eq Univ (weak_fixed_point fixed_pt) (apply fixed_pt (weak_fixed_point fixed_pt)))
.
#Univ ##.
#X ##.
#Y ##.
#Z ##.
#apply ##.
#b ##.
#c ##.
#fixed_pt ##.
#i ##.
#s ##.
#weak_fixed_point ##.
#H0 ##.
#H1 ##.
#H2 ##.
#H3 ##.
#H4 ##.
nauto by H0,H1,H2,H3,H4 ##;
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)

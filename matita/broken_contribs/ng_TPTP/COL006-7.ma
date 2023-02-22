include "logic/equality.ma".

(* Inclusion of: COL006-7.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : COL006-7 : TPTP v3.7.0. Released v2.1.0. *)

(*  Domain   : Combinatory Logic *)

(*  Problem  : Strong fixed point for S and K *)

(*  Version  : [WM88] (equality) axioms. *)

(*             Theorem formulation : The fixed point is provided and checked. *)

(*  English  : The strong fixed point property holds for the set  *)

(*             P consisting of the combinators S and K alone, where *)

(*             ((Sx)y)z = (xz)(yz), (Kx)y = x. *)

(*  Refs     : [WM88]  Wos & McCune (1988), Challenge Problems Focusing on Eq *)

(*  Source   : [TPTP] *)

(*  Names    :  *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.56 v3.4.0, 0.50 v3.3.0, 0.64 v3.1.0, 0.78 v2.7.0, 0.91 v2.6.0, 0.67 v2.5.0, 0.50 v2.4.0, 0.67 v2.2.1, 0.88 v2.2.0, 0.80 v2.1.0 *)

(*  Syntax   : Number of clauses     :    4 (   0 non-Horn;   4 unit;   2 RR) *)

(*             Number of atoms       :    4 (   4 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    5 (   4 constant; 0-2 arity) *)

(*             Number of variables   :    5 (   1 singleton) *)

(*             Maximal term depth    :    8 (   3 average) *)

(*  Comments :  *)

(* -------------------------------------------------------------------------- *)
ntheorem prove_strong_fixed_point:
 (∀Univ:Type.∀X:Univ.∀Y:Univ.∀Z:Univ.
∀apply:∀_:Univ.∀_:Univ.Univ.
∀fixed_pt:Univ.
∀k:Univ.
∀s:Univ.
∀strong_fixed_point:Univ.
∀H0:eq Univ strong_fixed_point (apply (apply s (apply k (apply (apply (apply s s) (apply (apply s k) k)) (apply (apply s s) (apply s k))))) (apply (apply s (apply k s)) k)).
∀H1:∀X:Univ.∀Y:Univ.eq Univ (apply (apply k X) Y) X.
∀H2:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (apply (apply (apply s X) Y) Z) (apply (apply X Z) (apply Y Z)).eq Univ (apply strong_fixed_point fixed_pt) (apply fixed_pt (apply strong_fixed_point fixed_pt)))
.
#Univ ##.
#X ##.
#Y ##.
#Z ##.
#apply ##.
#fixed_pt ##.
#k ##.
#s ##.
#strong_fixed_point ##.
#H0 ##.
#H1 ##.
#H2 ##.
nauto by H0,H1,H2 ##;
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)

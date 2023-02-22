include "logic/equality.ma".

(* Inclusion of: COL066-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : COL066-1 : TPTP v3.7.0. Released v1.0.0. *)

(*  Domain   : Combinatory Logic *)

(*  Problem  : Find combinator equivalent to P from B, Q and W *)

(*  Version  : [WM88] (equality) axioms. *)

(*  English  : Construct from B, Q and W alone a combinator that behaves as  *)

(*             the combinator P does, where ((Bx)y)z = x(yz), ((Qx)y)z =  *)

(*             y(xz), (Wx)y = (xy)y, (((Px)y)y)z = (xy)((xy)z) *)

(*  Refs     : [WM88]  Wos & McCune (1988), Challenge Problems Focusing on Eq *)

(*           : [WW+90] Wos et al. (1990), Automated Reasoning Contributes to  *)

(*  Source   : [WW+90] *)

(*  Names    : CL-7 [WW+90] *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.78 v3.4.0, 0.88 v3.3.0, 0.93 v3.1.0, 0.89 v2.7.0, 0.82 v2.6.0, 0.67 v2.5.0, 0.25 v2.4.0, 0.00 v2.3.0, 0.33 v2.2.1, 0.89 v2.2.0, 0.86 v2.1.0, 1.00 v2.0.0 *)

(*  Syntax   : Number of clauses     :    4 (   0 non-Horn;   4 unit;   1 RR) *)

(*             Number of atoms       :    4 (   4 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    7 (   3 constant; 0-2 arity) *)

(*             Number of variables   :    9 (   0 singleton) *)

(*             Maximal term depth    :    6 (   4 average) *)

(*  Comments :  *)

(* -------------------------------------------------------------------------- *)
ntheorem prove_p_combinator:
 (∀Univ:Type.∀X:Univ.∀Y:Univ.∀Z:Univ.
∀apply:∀_:Univ.∀_:Univ.Univ.
∀b:Univ.
∀f:∀_:Univ.Univ.
∀g:∀_:Univ.Univ.
∀h:∀_:Univ.Univ.
∀q:Univ.
∀w:Univ.
∀H0:∀X:Univ.∀Y:Univ.eq Univ (apply (apply w X) Y) (apply (apply X Y) Y).
∀H1:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (apply (apply (apply q X) Y) Z) (apply Y (apply X Z)).
∀H2:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (apply (apply (apply b X) Y) Z) (apply X (apply Y Z)).∃X:Univ.eq Univ (apply (apply (apply (apply X (f X)) (g X)) (g X)) (h X)) (apply (apply (f X) (g X)) (apply (apply (f X) (g X)) (h X))))
.
#Univ ##.
#X ##.
#Y ##.
#Z ##.
#apply ##.
#b ##.
#f ##.
#g ##.
#h ##.
#q ##.
#w ##.
#H0 ##.
#H1 ##.
#H2 ##.
napply (ex_intro ? ? ? ?) ##[
##2:
nauto by H0,H1,H2 ##;
##| ##skip ##]
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)

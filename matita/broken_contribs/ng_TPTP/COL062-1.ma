include "logic/equality.ma".

(* Inclusion of: COL062-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : COL062-1 : TPTP v3.7.0. Released v1.0.0. *)

(*  Domain   : Combinatory Logic *)

(*  Problem  : Find combinator equivalent to C from B and T *)

(*  Version  : [WM88] (equality) axioms. *)

(*  English  : Construct from B and T alone a combinator that behaves as the  *)

(*             combinator C does, where ((Bx)y)z = x(yz), (Tx)y = yx,  *)

(*             ((Cx)y)z = (xz)y *)

(*  Refs     : [WM88]  Wos & McCune (1988), Challenge Problems Focusing on Eq *)

(*           : [WW+90] Wos et al. (1990), Automated Reasoning Contributes to  *)

(*  Source   : [WW+90] *)

(*  Names    : CL-3 [WW+90] *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.33 v3.4.0, 0.50 v3.1.0, 0.44 v2.7.0, 0.36 v2.6.0, 0.17 v2.5.0, 0.00 v2.2.1, 0.44 v2.2.0, 0.57 v2.1.0, 1.00 v2.0.0 *)

(*  Syntax   : Number of clauses     :    3 (   0 non-Horn;   3 unit;   1 RR) *)

(*             Number of atoms       :    3 (   3 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    6 (   2 constant; 0-2 arity) *)

(*             Number of variables   :    6 (   0 singleton) *)

(*             Maximal term depth    :    5 (   4 average) *)

(*  Comments :  *)

(* -------------------------------------------------------------------------- *)
ntheorem prove_c_combinator:
 (∀Univ:Type.∀X:Univ.∀Y:Univ.∀Z:Univ.
∀apply:∀_:Univ.∀_:Univ.Univ.
∀b:Univ.
∀f:∀_:Univ.Univ.
∀g:∀_:Univ.Univ.
∀h:∀_:Univ.Univ.
∀t:Univ.
∀H0:∀X:Univ.∀Y:Univ.eq Univ (apply (apply t X) Y) (apply Y X).
∀H1:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (apply (apply (apply b X) Y) Z) (apply X (apply Y Z)).∃X:Univ.eq Univ (apply (apply (apply X (f X)) (g X)) (h X)) (apply (apply (f X) (h X)) (g X)))
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
#t ##.
#H0 ##.
#H1 ##.
napply (ex_intro ? ? ? ?) ##[
##2:
nauto by H0,H1 ##;
##| ##skip ##]
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)

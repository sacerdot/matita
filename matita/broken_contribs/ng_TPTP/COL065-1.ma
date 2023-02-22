include "logic/equality.ma".

(* Inclusion of: COL065-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : COL065-1 : TPTP v3.7.0. Released v1.0.0. *)

(*  Domain   : Combinatory Logic *)

(*  Problem  : Find combinator equivalent to G from B and T *)

(*  Version  : [WM88] (equality) axioms. *)

(*  English  : Construct from B and T alone a combinator that behaves as the  *)

(*             combinator G does, where ((Bx)y)z = x(yz), (Tx)y = yx,  *)

(*             (((Gx)y)z)w = (xw)(yz) *)

(*  Refs     : [WM88]  Wos & McCune (1988), Challenge Problems Focusing on Eq *)

(*           : [WW+90] Wos et al. (1990), Automated Reasoning Contributes to  *)

(*  Source   : [WW+90] *)

(*  Names    : CL-6 [WW+90] *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.56 v3.4.0, 0.62 v3.3.0, 0.64 v3.2.0, 0.71 v3.1.0, 0.56 v2.7.0, 0.45 v2.6.0, 0.33 v2.5.0, 0.00 v2.4.0, 0.00 v2.2.1, 0.89 v2.2.0, 0.86 v2.1.0, 1.00 v2.0.0 *)

(*  Syntax   : Number of clauses     :    3 (   0 non-Horn;   3 unit;   1 RR) *)

(*             Number of atoms       :    3 (   3 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    7 (   2 constant; 0-2 arity) *)

(*             Number of variables   :    6 (   0 singleton) *)

(*             Maximal term depth    :    6 (   4 average) *)

(*  Comments :  *)

(* -------------------------------------------------------------------------- *)
ntheorem prove_g_combinator:
 (∀Univ:Type.∀X:Univ.∀Y:Univ.∀Z:Univ.
∀apply:∀_:Univ.∀_:Univ.Univ.
∀b:Univ.
∀f:∀_:Univ.Univ.
∀g:∀_:Univ.Univ.
∀h:∀_:Univ.Univ.
∀i:∀_:Univ.Univ.
∀t:Univ.
∀H0:∀X:Univ.∀Y:Univ.eq Univ (apply (apply t X) Y) (apply Y X).
∀H1:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (apply (apply (apply b X) Y) Z) (apply X (apply Y Z)).∃X:Univ.eq Univ (apply (apply (apply (apply X (f X)) (g X)) (h X)) (i X)) (apply (apply (f X) (i X)) (apply (g X) (h X))))
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
#i ##.
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

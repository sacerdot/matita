include "logic/equality.ma".

(* Inclusion of: COL063-2.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : COL063-2 : TPTP v3.7.0. Bugfixed v1.2.0. *)

(*  Domain   : Combinatory Logic *)

(*  Problem  : Find combinator equivalent to F from B and T *)

(*  Version  : [WM88] (equality) axioms. *)

(*             Theorem formulation : The combinator is provided and checked. *)

(*  English  : Construct from B and T alone a combinator that behaves as the  *)

(*             combinator F does, where ((Bx)y)z = x(yz), (Tx)y = yx,  *)

(*             ((Fx)y)z = (zy)x. *)

(*  Refs     : [WM88]  Wos & McCune (1988), Challenge Problems Focusing on Eq *)

(*           : [WW+90] Wos et al. (1990), Automated Reasoning Contributes to  *)

(*  Source   : [TPTP] *)

(*  Names    :  *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.11 v3.4.0, 0.12 v3.3.0, 0.00 v2.2.1, 0.11 v2.2.0, 0.14 v2.1.0, 0.00 v2.0.0 *)

(*  Syntax   : Number of clauses     :    3 (   0 non-Horn;   3 unit;   1 RR) *)

(*             Number of atoms       :    3 (   3 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    6 (   5 constant; 0-2 arity) *)

(*             Number of variables   :    5 (   0 singleton) *)

(*             Maximal term depth    :    8 (   4 average) *)

(*  Comments :  *)

(*  Bugfixes : v1.2.0 : Redundant [fgh]_substitution axioms removed. *)

(* -------------------------------------------------------------------------- *)

(* ----This is the F equivalent *)
ntheorem prove_f_combinator:
 (∀Univ:Type.∀X:Univ.∀Y:Univ.∀Z:Univ.
∀apply:∀_:Univ.∀_:Univ.Univ.
∀b:Univ.
∀t:Univ.
∀x:Univ.
∀y:Univ.
∀z:Univ.
∀H0:∀X:Univ.∀Y:Univ.eq Univ (apply (apply t X) Y) (apply Y X).
∀H1:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (apply (apply (apply b X) Y) Z) (apply X (apply Y Z)).eq Univ (apply (apply (apply (apply (apply b (apply t t)) (apply (apply b b) (apply (apply b b) t))) x) y) z) (apply (apply z y) x))
.
#Univ ##.
#X ##.
#Y ##.
#Z ##.
#apply ##.
#b ##.
#t ##.
#x ##.
#y ##.
#z ##.
#H0 ##.
#H1 ##.
nauto by H0,H1 ##;
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)

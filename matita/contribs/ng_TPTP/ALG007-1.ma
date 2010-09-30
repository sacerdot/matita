include "logic/equality.ma".

(* Inclusion of: ALG007-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : ALG007-1 : TPTP v3.7.0. Released v2.2.0. *)

(*  Domain   : General Algebra *)

(*  Problem  : Simplification of Kalman's set difference basis (part 2) *)

(*  Version  : [MP96] (equality) axioms : Especial. *)

(*  English  : This is part 2 of a proof that one of the axioms in Kalman's *)

(*             basis for set difference can be simplified. *)

(*  Refs     : [McC98] McCune (1998), Email to G. Sutcliffe *)

(*           : [MP96]  McCune & Padmanabhan (1996), Automated Deduction in Eq *)

(*  Source   : [McC98] *)

(*  Names    : SD-3-b [MP96] *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.00 v3.4.0, 0.12 v3.3.0, 0.00 v3.1.0, 0.11 v2.7.0, 0.00 v2.2.1 *)

(*  Syntax   : Number of clauses     :    4 (   0 non-Horn;   4 unit;   1 RR) *)

(*             Number of atoms       :    4 (   4 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    4 (   3 constant; 0-2 arity) *)

(*             Number of variables   :    7 (   1 singleton) *)

(*             Maximal term depth    :    3 (   3 average) *)

(*  Comments : *)

(* -------------------------------------------------------------------------- *)

(* ----Kalman's axioms for set difference: *)

(* ----Simplified third axiom: *)

(* ----Denial of original third axiom: *)
ntheorem prove_set_difference_3:
 (∀Univ:Type.∀X:Univ.∀Y:Univ.∀Z:Univ.
∀a:Univ.
∀b:Univ.
∀c:Univ.
∀difference:∀_:Univ.∀_:Univ.Univ.
∀H0:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (difference (difference X Y) Z) (difference (difference X Z) Y).
∀H1:∀X:Univ.∀Y:Univ.eq Univ (difference X (difference X Y)) (difference Y (difference Y X)).
∀H2:∀X:Univ.∀Y:Univ.eq Univ (difference X (difference Y X)) X.eq Univ (difference (difference a b) c) (difference (difference a c) (difference b c)))
.
#Univ ##.
#X ##.
#Y ##.
#Z ##.
#a ##.
#b ##.
#c ##.
#difference ##.
#H0 ##.
#H1 ##.
#H2 ##.
nauto by H0,H1,H2 ##;
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)

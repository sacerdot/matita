include "logic/equality.ma".

(* Inclusion of: ALG005-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : ALG005-1 : TPTP v3.7.0. Released v2.2.0. *)

(*  Domain   : General Algebra *)

(*  Problem  : Associativity of intersection in terms of set difference. *)

(*  Version  : [MP96] (equality) axioms : Especial. *)

(*  English  : Starting with Kalman's basis for families of sets closed under *)

(*             set difference, we define intersection and show it to be *)

(*             associative. *)

(*  Refs     : [McC98] McCune (1998), Email to G. Sutcliffe *)

(*           : [MP96]  McCune & Padmanabhan (1996), Automated Deduction in Eq *)

(*  Source   : [McC98] *)

(*  Names    : SD-2-a [MP96] *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.11 v3.4.0, 0.12 v3.3.0, 0.07 v3.1.0, 0.22 v2.7.0, 0.00 v2.2.1 *)

(*  Syntax   : Number of clauses     :    5 (   0 non-Horn;   5 unit;   1 RR) *)

(*             Number of atoms       :    5 (   5 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    5 (   3 constant; 0-2 arity) *)

(*             Number of variables   :    9 (   1 singleton) *)

(*             Maximal term depth    :    3 (   3 average) *)

(*  Comments : *)

(* -------------------------------------------------------------------------- *)

(* ----Kalman's axioms for set difference: *)

(* ----Definition of intersection: *)

(* ----Denial of associativity: *)
ntheorem prove_associativity_of_multiply:
 (∀Univ:Type.∀X:Univ.∀Y:Univ.∀Z:Univ.
∀a:Univ.
∀b:Univ.
∀c:Univ.
∀difference:∀_:Univ.∀_:Univ.Univ.
∀multiply:∀_:Univ.∀_:Univ.Univ.
∀H0:∀X:Univ.∀Y:Univ.eq Univ (multiply X Y) (difference X (difference X Y)).
∀H1:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (difference (difference X Y) Z) (difference (difference X Z) (difference Y Z)).
∀H2:∀X:Univ.∀Y:Univ.eq Univ (difference X (difference X Y)) (difference Y (difference Y X)).
∀H3:∀X:Univ.∀Y:Univ.eq Univ (difference X (difference Y X)) X.eq Univ (multiply (multiply a b) c) (multiply a (multiply b c)))
.
#Univ ##.
#X ##.
#Y ##.
#Z ##.
#a ##.
#b ##.
#c ##.
#difference ##.
#multiply ##.
#H0 ##.
#H1 ##.
#H2 ##.
#H3 ##.
nauto by H0,H1,H2,H3 ##;
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)

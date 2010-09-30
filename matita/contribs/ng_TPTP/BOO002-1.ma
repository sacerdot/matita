include "logic/equality.ma".

(* Inclusion of: BOO002-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : BOO002-1 : TPTP v3.7.0. Released v1.0.0. *)

(*  Domain   : Boolean Algebra (Ternary) *)

(*  Problem  : In B3 algebra, X * X^-1 * Y = Y *)

(*  Version  : [OTTER] (equality) axioms : Reduced > Incomplete. *)

(*  English  :  *)

(*  Refs     : [LO85]  Lusk & Overbeek (1985), Reasoning about Equality *)

(*           : [Ove90] Overbeek (1990), ATP competition announced at CADE-10 *)

(*           : [Ove93] Overbeek (1993), The CADE-11 Competitions: A Personal  *)

(*           : [LM93]  Lusk & McCune (1993), Uniform Strategies: The CADE-11  *)

(*           : [Zha93] Zhang (1993), Automated Proofs of Equality Problems in *)

(*  Source   : [Ove90] *)

(*  Names    : Problem 5 [LO85] *)

(*           : CADE-11 Competition Eq-3 [Ove90] *)

(*           : THEOREM EQ-3 [LM93] *)

(*           : PROBLEM 3 [Zha93] *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.00 v3.3.0, 0.07 v3.1.0, 0.00 v2.7.0, 0.09 v2.6.0, 0.00 v2.2.1, 0.33 v2.2.0, 0.43 v2.1.0, 0.38 v2.0.0 *)

(*  Syntax   : Number of clauses     :    5 (   0 non-Horn;   5 unit;   1 RR) *)

(*             Number of atoms       :    5 (   5 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    4 (   2 constant; 0-3 arity) *)

(*             Number of variables   :   11 (   2 singleton) *)

(*             Maximal term depth    :    3 (   2 average) *)

(*  Comments :  *)

(* -------------------------------------------------------------------------- *)

(* ----Don't include ternary Boolean algebra axioms, as one is omitted  *)

(*  include('axioms/BOO001-0.ax'). *)

(* -------------------------------------------------------------------------- *)

(* ----This axiom is omitted  *)

(*  input_clause(right_inverse,axiom, *)

(*      [++equal(multiply(X,Y,inverse(Y)),X)]). *)
ntheorem prove_equation:
 (∀Univ:Type.∀V:Univ.∀W:Univ.∀X:Univ.∀Y:Univ.∀Z:Univ.
∀a:Univ.
∀b:Univ.
∀inverse:∀_:Univ.Univ.
∀multiply:∀_:Univ.∀_:Univ.∀_:Univ.Univ.
∀H0:∀X:Univ.∀Y:Univ.eq Univ (multiply (inverse Y) Y X) X.
∀H1:∀X:Univ.∀Y:Univ.eq Univ (multiply X X Y) X.
∀H2:∀X:Univ.∀Y:Univ.eq Univ (multiply Y X X) X.
∀H3:∀V:Univ.∀W:Univ.∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (multiply (multiply V W X) Y (multiply V W Z)) (multiply V W (multiply X Y Z)).eq Univ (multiply a (inverse a) b) b)
.
#Univ ##.
#V ##.
#W ##.
#X ##.
#Y ##.
#Z ##.
#a ##.
#b ##.
#inverse ##.
#multiply ##.
#H0 ##.
#H1 ##.
#H2 ##.
#H3 ##.
nauto by H0,H1,H2,H3 ##;
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)

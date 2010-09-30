include "logic/equality.ma".

(* Inclusion of: GRP445-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : GRP445-1 : TPTP v3.7.0. Released v2.6.0. *)

(*  Domain   : Group Theory *)

(*  Problem  : Axiom for group theory, in division, part 1 *)

(*  Version  : [McC93] (equality) axioms. *)

(*  English  :  *)

(*  Refs     : [HN52]  Higman & Neumann (1952), Groups as Groupoids with One  *)

(*           : [McC93] McCune (1993), Single Axioms for Groups and Abelian Gr *)

(*  Source   : [TPTP] *)

(*  Names    :  *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.00 v2.6.0 *)

(*  Syntax   : Number of clauses     :    4 (   0 non-Horn;   4 unit;   1 RR) *)

(*             Number of atoms       :    4 (   4 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    5 (   2 constant; 0-2 arity) *)

(*             Number of variables   :    8 (   0 singleton) *)

(*             Maximal term depth    :    6 (   3 average) *)

(*  Comments : A UEQ part of GRP063-1 *)

(* -------------------------------------------------------------------------- *)
ntheorem prove_these_axioms_1:
 (∀Univ:Type.∀A:Univ.∀B:Univ.∀C:Univ.
∀a1:Univ.
∀b1:Univ.
∀divide:∀_:Univ.∀_:Univ.Univ.
∀inverse:∀_:Univ.Univ.
∀multiply:∀_:Univ.∀_:Univ.Univ.
∀H0:∀A:Univ.∀B:Univ.eq Univ (inverse A) (divide (divide B B) A).
∀H1:∀A:Univ.∀B:Univ.∀C:Univ.eq Univ (multiply A B) (divide A (divide (divide C C) B)).
∀H2:∀A:Univ.∀B:Univ.∀C:Univ.eq Univ (divide A (divide (divide (divide (divide A A) B) C) (divide (divide (divide A A) A) C))) B.eq Univ (multiply (inverse a1) a1) (multiply (inverse b1) b1))
.
#Univ ##.
#A ##.
#B ##.
#C ##.
#a1 ##.
#b1 ##.
#divide ##.
#inverse ##.
#multiply ##.
#H0 ##.
#H1 ##.
#H2 ##.
nauto by H0,H1,H2 ##;
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)

include "logic/equality.ma".

(* Inclusion of: GRP534-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : GRP534-1 : TPTP v3.7.0. Released v2.6.0. *)

(*  Domain   : Group Theory (Abelian) *)

(*  Problem  : Axiom for Abelian group theory, in division, part 2 *)

(*  Version  : [McC93] (equality) axioms. *)

(*  English  :  *)

(*  Refs     : [McC93] McCune (1993), Single Axioms for Groups and Abelian Gr *)

(*  Source   : [TPTP] *)

(*  Names    :  *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.00 v2.6.0 *)

(*  Syntax   : Number of clauses     :    5 (   0 non-Horn;   5 unit;   1 RR) *)

(*             Number of atoms       :    5 (   5 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    6 (   3 constant; 0-2 arity) *)

(*             Number of variables   :    9 (   0 singleton) *)

(*             Maximal term depth    :    5 (   2 average) *)

(*  Comments : A UEQ part of GRP091-1 *)

(* -------------------------------------------------------------------------- *)
ntheorem prove_these_axioms_2:
 (∀Univ:Type.∀A:Univ.∀B:Univ.∀C:Univ.
∀a2:Univ.
∀b2:Univ.
∀divide:∀_:Univ.∀_:Univ.Univ.
∀identity:Univ.
∀inverse:∀_:Univ.Univ.
∀multiply:∀_:Univ.∀_:Univ.Univ.
∀H0:∀A:Univ.eq Univ identity (divide A A).
∀H1:∀A:Univ.∀B:Univ.eq Univ (inverse A) (divide (divide B B) A).
∀H2:∀A:Univ.∀B:Univ.∀C:Univ.eq Univ (multiply A B) (divide A (divide (divide C C) B)).
∀H3:∀A:Univ.∀B:Univ.∀C:Univ.eq Univ (divide (divide A (divide (divide A B) C)) B) C.eq Univ (multiply (multiply (inverse b2) b2) a2) a2)
.
#Univ ##.
#A ##.
#B ##.
#C ##.
#a2 ##.
#b2 ##.
#divide ##.
#identity ##.
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

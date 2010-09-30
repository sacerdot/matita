include "logic/equality.ma".

(* Inclusion of: GRP453-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : GRP453-1 : TPTP v3.7.0. Released v2.6.0. *)

(*  Domain   : Group Theory *)

(*  Problem  : Axiom for group theory, in division, part 3 *)

(*  Version  : [McC93] (equality) axioms. *)

(*  English  :  *)

(*  Refs     : [McC93] McCune (1993), Single Axioms for Groups and Abelian Gr *)

(*  Source   : [TPTP] *)

(*  Names    :  *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.33 v3.4.0, 0.38 v3.3.0, 0.21 v3.1.0, 0.11 v2.7.0, 0.27 v2.6.0 *)

(*  Syntax   : Number of clauses     :    4 (   0 non-Horn;   4 unit;   1 RR) *)

(*             Number of atoms       :    4 (   4 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    6 (   3 constant; 0-2 arity) *)

(*             Number of variables   :    8 (   0 singleton) *)

(*             Maximal term depth    :    8 (   3 average) *)

(*  Comments : A UEQ part of GRP065-1 *)

(* -------------------------------------------------------------------------- *)
ntheorem prove_these_axioms_3:
 (∀Univ:Type.∀A:Univ.∀B:Univ.∀C:Univ.
∀a3:Univ.
∀b3:Univ.
∀c3:Univ.
∀divide:∀_:Univ.∀_:Univ.Univ.
∀inverse:∀_:Univ.Univ.
∀multiply:∀_:Univ.∀_:Univ.Univ.
∀H0:∀A:Univ.∀B:Univ.eq Univ (inverse A) (divide (divide B B) A).
∀H1:∀A:Univ.∀B:Univ.∀C:Univ.eq Univ (multiply A B) (divide A (divide (divide C C) B)).
∀H2:∀A:Univ.∀B:Univ.∀C:Univ.eq Univ (divide (divide (divide A A) (divide A (divide B (divide (divide (divide A A) A) C)))) C) B.eq Univ (multiply (multiply a3 b3) c3) (multiply a3 (multiply b3 c3)))
.
#Univ ##.
#A ##.
#B ##.
#C ##.
#a3 ##.
#b3 ##.
#c3 ##.
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

include "logic/equality.ma".

(* Inclusion of: GRP480-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : GRP480-1 : TPTP v3.7.0. Released v2.6.0. *)

(*  Domain   : Group Theory *)

(*  Problem  : Axiom for group theory, in division and inverse, part 3 *)

(*  Version  : [McC93] (equality) axioms. *)

(*  English  :  *)

(*  Refs     : [McC93] McCune (1993), Single Axioms for Groups and Abelian Gr *)

(*  Source   : [TPTP] *)

(*  Names    :  *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.22 v3.4.0, 0.25 v3.3.0, 0.21 v3.1.0, 0.11 v2.7.0, 0.27 v2.6.0 *)

(*  Syntax   : Number of clauses     :    3 (   0 non-Horn;   3 unit;   1 RR) *)

(*             Number of atoms       :    3 (   3 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    6 (   3 constant; 0-2 arity) *)

(*             Number of variables   :    6 (   0 singleton) *)

(*             Maximal term depth    :    6 (   3 average) *)

(*  Comments : A UEQ part of GRP074-1 *)

(* -------------------------------------------------------------------------- *)
ntheorem prove_these_axioms_3:
 (∀Univ:Type.∀A:Univ.∀B:Univ.∀C:Univ.∀D:Univ.
∀a3:Univ.
∀b3:Univ.
∀c3:Univ.
∀divide:∀_:Univ.∀_:Univ.Univ.
∀inverse:∀_:Univ.Univ.
∀multiply:∀_:Univ.∀_:Univ.Univ.
∀H0:∀A:Univ.∀B:Univ.eq Univ (multiply A B) (divide A (inverse B)).
∀H1:∀A:Univ.∀B:Univ.∀C:Univ.∀D:Univ.eq Univ (divide (inverse (divide (divide (divide A A) B) (divide C (divide B D)))) D) C.eq Univ (multiply (multiply a3 b3) c3) (multiply a3 (multiply b3 c3)))
.
#Univ ##.
#A ##.
#B ##.
#C ##.
#D ##.
#a3 ##.
#b3 ##.
#c3 ##.
#divide ##.
#inverse ##.
#multiply ##.
#H0 ##.
#H1 ##.
nauto by H0,H1 ##;
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)

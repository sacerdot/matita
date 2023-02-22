include "logic/equality.ma".

(* Inclusion of: GRP500-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : GRP500-1 : TPTP v3.7.0. Released v2.6.0. *)

(*  Domain   : Group Theory *)

(*  Problem  : Axiom for group theory, in double division and inverse, part 2 *)

(*  Version  : [McC93] (equality) axioms. *)

(*  English  :  *)

(*  Refs     : [McC93] McCune (1993), Single Axioms for Groups and Abelian Gr *)

(*  Source   : [TPTP] *)

(*  Names    :  *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.11 v3.4.0, 0.12 v3.3.0, 0.07 v3.1.0, 0.11 v2.7.0, 0.00 v2.6.0 *)

(*  Syntax   : Number of clauses     :    3 (   0 non-Horn;   3 unit;   1 RR) *)

(*             Number of atoms       :    3 (   3 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    5 (   2 constant; 0-2 arity) *)

(*             Number of variables   :    6 (   0 singleton) *)

(*             Maximal term depth    :    7 (   3 average) *)

(*  Comments : A UEQ part of GRP082-1 *)

(* -------------------------------------------------------------------------- *)
ntheorem prove_these_axioms_2:
 (∀Univ:Type.∀A:Univ.∀B:Univ.∀C:Univ.∀D:Univ.
∀a2:Univ.
∀b2:Univ.
∀double_divide:∀_:Univ.∀_:Univ.Univ.
∀inverse:∀_:Univ.Univ.
∀multiply:∀_:Univ.∀_:Univ.Univ.
∀H0:∀A:Univ.∀B:Univ.eq Univ (multiply A B) (inverse (double_divide B A)).
∀H1:∀A:Univ.∀B:Univ.∀C:Univ.∀D:Univ.eq Univ (double_divide (inverse A) (inverse (double_divide (inverse (double_divide A (double_divide B C))) (double_divide D (double_divide B D))))) C.eq Univ (multiply (multiply (inverse b2) b2) a2) a2)
.
#Univ ##.
#A ##.
#B ##.
#C ##.
#D ##.
#a2 ##.
#b2 ##.
#double_divide ##.
#inverse ##.
#multiply ##.
#H0 ##.
#H1 ##.
nauto by H0,H1 ##;
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)

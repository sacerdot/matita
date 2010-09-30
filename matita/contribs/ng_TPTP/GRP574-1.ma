include "logic/equality.ma".

(* Inclusion of: GRP574-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : GRP574-1 : TPTP v3.7.0. Released v2.6.0. *)

(*  Domain   : Group Theory (Abelian) *)

(*  Problem  : Axiom for Abelian group theory, in double div and id, part 2 *)

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

(*             Number of functors    :    5 (   2 constant; 0-2 arity) *)

(*             Number of variables   :    7 (   0 singleton) *)

(*             Maximal term depth    :    6 (   2 average) *)

(*  Comments : A UEQ part of GRP101-1 *)

(* -------------------------------------------------------------------------- *)
ntheorem prove_these_axioms_2:
 (∀Univ:Type.∀A:Univ.∀B:Univ.∀C:Univ.
∀a2:Univ.
∀double_divide:∀_:Univ.∀_:Univ.Univ.
∀identity:Univ.
∀inverse:∀_:Univ.Univ.
∀multiply:∀_:Univ.∀_:Univ.Univ.
∀H0:∀A:Univ.eq Univ identity (double_divide A (inverse A)).
∀H1:∀A:Univ.eq Univ (inverse A) (double_divide A identity).
∀H2:∀A:Univ.∀B:Univ.eq Univ (multiply A B) (double_divide (double_divide B A) identity).
∀H3:∀A:Univ.∀B:Univ.∀C:Univ.eq Univ (double_divide (double_divide A (double_divide (double_divide B (double_divide C A)) (double_divide C identity))) (double_divide identity identity)) B.eq Univ (multiply identity a2) a2)
.
#Univ ##.
#A ##.
#B ##.
#C ##.
#a2 ##.
#double_divide ##.
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

include "logic/equality.ma".

(* Inclusion of: GRP518-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : GRP518-1 : TPTP v3.7.0. Released v2.6.0. *)

(*  Domain   : Group Theory (Abelian) *)

(*  Problem  : Axiom for Abelian group theory, in product and inverse, part 2 *)

(*  Version  : [McC93] (equality) axioms. *)

(*  English  :  *)

(*  Refs     : [McC93] McCune (1993), Single Axioms for Groups and Abelian Gr *)

(*  Source   : [TPTP] *)

(*  Names    :  *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.00 v2.6.0 *)

(*  Syntax   : Number of clauses     :    2 (   0 non-Horn;   2 unit;   1 RR) *)

(*             Number of atoms       :    2 (   2 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    4 (   2 constant; 0-2 arity) *)

(*             Number of variables   :    3 (   0 singleton) *)

(*             Maximal term depth    :    6 (   3 average) *)

(*  Comments : A UEQ part of GRP087-1 *)

(* -------------------------------------------------------------------------- *)
ntheorem prove_these_axioms_2:
 (∀Univ:Type.∀A:Univ.∀B:Univ.∀C:Univ.
∀a2:Univ.
∀b2:Univ.
∀inverse:∀_:Univ.Univ.
∀multiply:∀_:Univ.∀_:Univ.Univ.
∀H0:∀A:Univ.∀B:Univ.∀C:Univ.eq Univ (multiply A (multiply (multiply (inverse (multiply A B)) C) B)) C.eq Univ (multiply (multiply (inverse b2) b2) a2) a2)
.
#Univ ##.
#A ##.
#B ##.
#C ##.
#a2 ##.
#b2 ##.
#inverse ##.
#multiply ##.
#H0 ##.
nauto by H0 ##;
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)

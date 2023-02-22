include "logic/equality.ma".

(* Inclusion of: GRP412-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : GRP412-1 : TPTP v3.7.0. Released v2.6.0. *)

(*  Domain   : Group Theory *)

(*  Problem  : Axiom for group theory, in product & inverse, part 1 *)

(*  Version  : [McC93] (equality) axioms. *)

(*  English  :  *)

(*  Refs     : [Kun92] Kunen (1992), Single Axioms for Groups *)

(*           : [McC93] McCune (1993), Single Axioms for Groups and Abelian Gr *)

(*  Source   : [TPTP] *)

(*  Names    :  *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.00 v3.4.0, 0.12 v3.3.0, 0.00 v2.6.0 *)

(*  Syntax   : Number of clauses     :    2 (   0 non-Horn;   2 unit;   1 RR) *)

(*             Number of atoms       :    2 (   2 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    4 (   2 constant; 0-2 arity) *)

(*             Number of variables   :    3 (   0 singleton) *)

(*             Maximal term depth    :   10 (   4 average) *)

(*  Comments : A UEQ part of GRP052-1 *)

(* -------------------------------------------------------------------------- *)
ntheorem prove_these_axioms_1:
 (∀Univ:Type.∀A:Univ.∀B:Univ.∀C:Univ.
∀a1:Univ.
∀b1:Univ.
∀inverse:∀_:Univ.Univ.
∀multiply:∀_:Univ.∀_:Univ.Univ.
∀H0:∀A:Univ.∀B:Univ.∀C:Univ.eq Univ (multiply A (inverse (multiply (multiply (multiply (inverse B) B) (inverse (multiply (inverse (multiply A (inverse B))) C))) B))) C.eq Univ (multiply (inverse a1) a1) (multiply (inverse b1) b1))
.
#Univ ##.
#A ##.
#B ##.
#C ##.
#a1 ##.
#b1 ##.
#inverse ##.
#multiply ##.
#H0 ##.
nauto by H0 ##;
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)

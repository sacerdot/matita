include "logic/equality.ma".

(* Inclusion of: GRP432-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : GRP432-1 : TPTP v3.7.0. Released v2.6.0. *)

(*  Domain   : Group Theory *)

(*  Problem  : Axiom for group theory, in product & inverse, part 3 *)

(*  Version  : [McC93] (equality) axioms. *)

(*  English  :  *)

(*  Refs     : [LW92]  Lusk & Wos (1992), Benchmark Problems in Which Equalit *)

(*           : [McC93] McCune (1993), Single Axioms for Groups and Abelian Gr *)

(*  Source   : [TPTP] *)

(*  Names    :  *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.11 v3.4.0, 0.12 v3.3.0, 0.00 v2.6.0 *)

(*  Syntax   : Number of clauses     :    2 (   0 non-Horn;   2 unit;   1 RR) *)

(*             Number of atoms       :    2 (   2 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    5 (   3 constant; 0-2 arity) *)

(*             Number of variables   :    4 (   0 singleton) *)

(*             Maximal term depth    :    8 (   4 average) *)

(*  Comments : A UEQ part of GRP058-1 *)

(* -------------------------------------------------------------------------- *)
ntheorem prove_these_axioms_3:
 (∀Univ:Type.∀A:Univ.∀B:Univ.∀C:Univ.∀D:Univ.
∀a3:Univ.
∀b3:Univ.
∀c3:Univ.
∀inverse:∀_:Univ.Univ.
∀multiply:∀_:Univ.∀_:Univ.Univ.
∀H0:∀A:Univ.∀B:Univ.∀C:Univ.∀D:Univ.eq Univ (multiply A (inverse (multiply B (multiply (multiply (multiply C (inverse C)) (inverse (multiply D B))) A)))) D.eq Univ (multiply (multiply a3 b3) c3) (multiply a3 (multiply b3 c3)))
.
#Univ ##.
#A ##.
#B ##.
#C ##.
#D ##.
#a3 ##.
#b3 ##.
#c3 ##.
#inverse ##.
#multiply ##.
#H0 ##.
nauto by H0 ##;
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)

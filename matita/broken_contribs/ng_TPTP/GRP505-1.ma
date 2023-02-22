include "logic/equality.ma".

(* Inclusion of: GRP505-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : GRP505-1 : TPTP v3.7.0. Released v2.6.0. *)

(*  Domain   : Group Theory (Abelian) *)

(*  Problem  : Axiom for Abelian group theory, in product and inverse, part 1 *)

(*  Version  : [McC93] (equality) axioms. *)

(*  English  :  *)

(*  Refs     : [Neu81] Neumann (1981), Another Single Law for Groups *)

(*           : [LW92]  Lusk & Wos (1992), Benchmark Problems in Which Equalit *)

(*           : [McC93] McCune (1993), Single Axioms for Groups and Abelian Gr *)

(*  Source   : [TPTP] *)

(*  Names    :  *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.56 v3.4.0, 0.50 v3.3.0, 0.57 v3.2.0, 0.50 v3.1.0, 0.44 v2.7.0, 0.64 v2.6.0 *)

(*  Syntax   : Number of clauses     :    2 (   0 non-Horn;   2 unit;   1 RR) *)

(*             Number of atoms       :    2 (   2 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    4 (   2 constant; 0-2 arity) *)

(*             Number of variables   :    6 (   0 singleton) *)

(*             Maximal term depth    :   10 (   4 average) *)

(*  Comments : A UEQ part of GRP084-1 *)

(* -------------------------------------------------------------------------- *)
ntheorem prove_these_axioms_1:
 (∀Univ:Type.∀A:Univ.∀B:Univ.∀C:Univ.∀D:Univ.∀E:Univ.∀F:Univ.
∀a1:Univ.
∀b1:Univ.
∀inverse:∀_:Univ.Univ.
∀multiply:∀_:Univ.∀_:Univ.Univ.
∀H0:∀A:Univ.∀B:Univ.∀C:Univ.∀D:Univ.∀E:Univ.∀F:Univ.eq Univ (multiply (inverse (multiply (inverse (multiply (inverse (multiply A B)) (multiply B A))) (multiply (inverse (multiply C D)) (multiply C (inverse (multiply (multiply E (inverse F)) (inverse D))))))) F) E.eq Univ (multiply (inverse a1) a1) (multiply (inverse b1) b1))
.
#Univ ##.
#A ##.
#B ##.
#C ##.
#D ##.
#E ##.
#F ##.
#a1 ##.
#b1 ##.
#inverse ##.
#multiply ##.
#H0 ##.
nauto by H0 ##;
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)

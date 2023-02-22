include "logic/equality.ma".

(* Inclusion of: GRP512-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : GRP512-1 : TPTP v3.7.0. Bugfixed v2.7.0. *)

(*  Domain   : Group Theory (Abelian) *)

(*  Problem  : Axiom for Abelian group theory, in product and inverse, part 4 *)

(*  Version  : [McC93] (equality) axioms. *)

(*  English  :  *)

(*  Refs     : [LW92]  Lusk & Wos (1992), Benchmark Problems in Which Equalit *)

(*           : [McC93] McCune (1993), Single Axioms for Groups and Abelian Gr *)

(*  Source   : [TPTP] *)

(*  Names    :  *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.11 v3.4.0, 0.12 v3.3.0, 0.00 v2.7.0 *)

(*  Syntax   : Number of clauses     :    2 (   0 non-Horn;   2 unit;   1 RR) *)

(*             Number of atoms       :    2 (   2 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    4 (   2 constant; 0-2 arity) *)

(*             Number of variables   :    3 (   0 singleton) *)

(*             Maximal term depth    :    4 (   2 average) *)

(*  Comments : A UEQ part of GRP085-1 *)

(*  Bugfixes : v2.7.0 - Grounded conjecture *)

(* -------------------------------------------------------------------------- *)
ntheorem prove_these_axioms_4:
 (∀Univ:Type.∀A:Univ.∀B:Univ.∀C:Univ.
∀a:Univ.
∀b:Univ.
∀inverse:∀_:Univ.Univ.
∀multiply:∀_:Univ.∀_:Univ.Univ.
∀H0:∀A:Univ.∀B:Univ.∀C:Univ.eq Univ (multiply (multiply (multiply A B) C) (inverse (multiply A C))) B.eq Univ (multiply a b) (multiply b a))
.
#Univ ##.
#A ##.
#B ##.
#C ##.
#a ##.
#b ##.
#inverse ##.
#multiply ##.
#H0 ##.
nauto by H0 ##;
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)

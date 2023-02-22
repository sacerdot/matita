include "logic/equality.ma".

(* Inclusion of: GRP207-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : GRP207-1 : TPTP v3.7.0. Released v2.4.0. *)

(*  Domain   : Group Theory *)

(*  Problem  : Single non-axiom for group theory, in product & inverse *)

(*  Version  : [McC93] (equality) axioms. *)

(*  English  : This is a single axiom for group theory, in terms of product  *)

(*             and inverse. *)

(*  Refs     : [Pel98] Peltier (1998), A New Method for Automated Finite Mode *)

(*           : [McC93] McCune (1993), Single Axioms for Groups and Abelian Gr *)

(*  Source   : [Pel98] *)

(*  Names    : 4.2.2 [Pel98] *)

(*  Status   : Satisfiable *)

(*  Rating   : 0.33 v3.2.0, 0.67 v3.1.0, 0.33 v2.4.0 *)

(*  Syntax   : Number of clauses     :    2 (   0 non-Horn;   2 unit;   1 RR) *)

(*             Number of atoms       :    2 (   2 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    6 (   4 constant; 0-2 arity) *)

(*             Number of variables   :    3 (   0 singleton) *)

(*             Maximal term depth    :    8 (   4 average) *)

(*  Comments :  *)

(* -------------------------------------------------------------------------- *)
ntheorem try_prove_this_axiom:
 (∀Univ:Type.∀U:Univ.∀Y:Univ.∀Z:Univ.
∀inverse:∀_:Univ.Univ.
∀multiply:∀_:Univ.∀_:Univ.Univ.
∀u:Univ.
∀x:Univ.
∀y:Univ.
∀z:Univ.
∀H0:∀U:Univ.∀Y:Univ.∀Z:Univ.eq Univ (multiply U (inverse (multiply Y (multiply (multiply (multiply Z (inverse Z)) (inverse (multiply U Y))) U)))) U.eq Univ (multiply x (inverse (multiply y (multiply (multiply (multiply z (inverse z)) (inverse (multiply u y))) x)))) u)
.
#Univ ##.
#U ##.
#Y ##.
#Z ##.
#inverse ##.
#multiply ##.
#u ##.
#x ##.
#y ##.
#z ##.
#H0 ##.
nauto by H0 ##;
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)

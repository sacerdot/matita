include "logic/equality.ma".

(* Inclusion of: ROB002-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : ROB002-1 : TPTP v3.7.0. Released v1.0.0. *)

(*  Domain   : Robbins Algebra *)

(*  Problem  : --X = X => Boolean *)

(*  Version  : [Win90] (equality) axioms. *)

(*  English  : If --X = X then the algebra is Boolean. *)

(*  Refs     : [HMT71] Henkin et al. (1971), Cylindrical Algebras *)

(*           : [Win90] Winker (1990), Robbins Algebra: Conditions that make a *)

(*  Source   : [Win90] *)

(*  Names    : Lemma 2.1 [Win90] *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.00 v2.2.1, 0.11 v2.2.0, 0.14 v2.1.0, 0.13 v2.0.0 *)

(*  Syntax   : Number of clauses     :    5 (   0 non-Horn;   5 unit;   1 RR) *)

(*             Number of atoms       :    5 (   5 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    4 (   2 constant; 0-2 arity) *)

(*             Number of variables   :    8 (   0 singleton) *)

(*             Maximal term depth    :    6 (   3 average) *)

(*  Comments : Commutativity, associativity, and Huntington's axiom  *)

(*             axiomatize Boolean algebra. *)

(* -------------------------------------------------------------------------- *)

(* ----Include axioms for Robbins algebra  *)

(* Inclusion of: Axioms/ROB001-0.ax *)

(* -------------------------------------------------------------------------- *)

(*  File     : ROB001-0 : TPTP v3.7.0. Released v1.0.0. *)

(*  Domain   : Robbins algebra *)

(*  Axioms   : Robbins algebra axioms *)

(*  Version  : [Win90] (equality) axioms. *)

(*  English  :  *)

(*  Refs     : [HMT71] Henkin et al. (1971), Cylindrical Algebras *)

(*           : [Win90] Winker (1990), Robbins Algebra: Conditions that make a *)

(*  Source   : [OTTER] *)

(*  Names    : Lemma 2.2 [Win90] *)

(*  Status   :  *)

(*  Syntax   : Number of clauses    :    3 (   0 non-Horn;   3 unit;   0 RR) *)

(*             Number of atoms      :    3 (   3 equality) *)

(*             Maximal clause size  :    1 (   1 average) *)

(*             Number of predicates :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors   :    2 (   0 constant; 1-2 arity) *)

(*             Number of variables  :    7 (   0 singleton) *)

(*             Maximal term depth   :    6 (   3 average) *)

(*  Comments :  *)

(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
ntheorem prove_huntingtons_axiom:
 (∀Univ:Type.∀X:Univ.∀Y:Univ.∀Z:Univ.
∀a:Univ.
∀add:∀_:Univ.∀_:Univ.Univ.
∀b:Univ.
∀negate:∀_:Univ.Univ.
∀H0:∀X:Univ.eq Univ (negate (negate X)) X.
∀H1:∀X:Univ.∀Y:Univ.eq Univ (negate (add (negate (add X Y)) (negate (add X (negate Y))))) X.
∀H2:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (add (add X Y) Z) (add X (add Y Z)).
∀H3:∀X:Univ.∀Y:Univ.eq Univ (add X Y) (add Y X).eq Univ (add (negate (add a (negate b))) (negate (add (negate a) (negate b)))) b)
.
#Univ ##.
#X ##.
#Y ##.
#Z ##.
#a ##.
#add ##.
#b ##.
#negate ##.
#H0 ##.
#H1 ##.
#H2 ##.
#H3 ##.
nauto by H0,H1,H2,H3 ##;
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)

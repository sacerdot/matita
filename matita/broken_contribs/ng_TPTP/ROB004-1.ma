include "logic/equality.ma".

(* Inclusion of: ROB004-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : ROB004-1 : TPTP v3.7.0. Released v1.0.0. *)

(*  Domain   : Robbins Algebra *)

(*  Problem  : c = -d, c + d=d, and c + c=c => Boolean *)

(*  Version  : [Win90] (equality) axioms. *)

(*  English  : If there exist c, d such that c = -d, c+d=d, and c+c=c, then  *)

(*             the algebra is Boolean. *)

(*  Refs     : [HMT71] Henkin et al. (1971), Cylindrical Algebras *)

(*           : [Win90] Winker (1990), Robbins Algebra: Conditions that make a *)

(*  Source   : [Win90] *)

(*  Names    : Lemma 2.3 [Win90] *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.00 v3.4.0, 0.12 v3.3.0, 0.00 v2.2.1, 0.22 v2.2.0, 0.29 v2.1.0, 0.38 v2.0.0 *)

(*  Syntax   : Number of clauses     :    7 (   0 non-Horn;   7 unit;   4 RR) *)

(*             Number of atoms       :    7 (   7 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    6 (   4 constant; 0-2 arity) *)

(*             Number of variables   :    7 (   0 singleton) *)

(*             Maximal term depth    :    6 (   2 average) *)

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
∀c:Univ.
∀d:Univ.
∀negate:∀_:Univ.Univ.
∀H0:eq Univ (add c c) c.
∀H1:eq Univ (add c d) d.
∀H2:eq Univ (negate d) c.
∀H3:∀X:Univ.∀Y:Univ.eq Univ (negate (add (negate (add X Y)) (negate (add X (negate Y))))) X.
∀H4:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (add (add X Y) Z) (add X (add Y Z)).
∀H5:∀X:Univ.∀Y:Univ.eq Univ (add X Y) (add Y X).eq Univ (add (negate (add a (negate b))) (negate (add (negate a) (negate b)))) b)
.
#Univ ##.
#X ##.
#Y ##.
#Z ##.
#a ##.
#add ##.
#b ##.
#c ##.
#d ##.
#negate ##.
#H0 ##.
#H1 ##.
#H2 ##.
#H3 ##.
#H4 ##.
#H5 ##.
nauto by H0,H1,H2,H3,H4,H5 ##;
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)

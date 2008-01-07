
include "logic/equality.ma".
(* Inclusion of: RNG024-7.p *)
(* -------------------------------------------------------------------------- *)
(*  File     : RNG024-7 : TPTP v3.1.1. Released v1.0.0. *)
(*  Domain   : Ring Theory (Alternative) *)
(*  Problem  : Right alternative *)
(*  Version  : [Ste87] (equality) axioms : Augmented. *)
(*             Theorem formulation : In terms of associators *)
(*  English  :  *)
(*  Refs     : [Ste87] Stevens (1987), Some Experiments in Nonassociative Rin *)
(*           : [Ste92] Stevens (1992), Unpublished Note *)
(*  Source   : [TPTP] *)
(*  Names    :  *)
(*  Status   : Unsatisfiable *)
(*  Rating   : 0.00 v2.2.1, 0.11 v2.2.0, 0.00 v2.1.0, 0.13 v2.0.0 *)
(*  Syntax   : Number of clauses     :   23 (   0 non-Horn;  23 unit;   1 RR) *)
(*             Number of atoms       :   23 (  23 equality) *)
(*             Maximal clause size   :    1 (   1 average) *)
(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)
(*             Number of functors    :    8 (   3 constant; 0-3 arity) *)
(*             Number of variables   :   45 (   2 singleton) *)
(*             Maximal term depth    :    5 (   3 average) *)
(*  Comments :  *)
(* -------------------------------------------------------------------------- *)
(* ----Include nonassociative ring axioms  *)
(* Inclusion of: Axioms/RNG003-0.ax *)
(* -------------------------------------------------------------------------- *)
(*  File     : RNG003-0 : TPTP v3.1.1. Released v1.0.0. *)
(*  Domain   : Ring Theory (Alternative) *)
(*  Axioms   : Alternative ring theory (equality) axioms *)
(*  Version  : [Ste87] (equality) axioms. *)
(*  English  :  *)
(*  Refs     : [Ste87] Stevens (1987), Some Experiments in Nonassociative Rin *)
(*  Source   : [Ste87] *)
(*  Names    :  *)
(*  Status   :  *)
(*  Syntax   : Number of clauses    :   15 (   0 non-Horn;  15 unit;   0 RR) *)
(*             Number of literals   :   15 (  15 equality) *)
(*             Maximal clause size  :    1 (   1 average) *)
(*             Number of predicates :    1 (   0 propositional; 2-2 arity) *)
(*             Number of functors   :    6 (   1 constant; 0-3 arity) *)
(*             Number of variables  :   27 (   2 singleton) *)
(*             Maximal term depth   :    5 (   2 average) *)
(*  Comments :  *)
(* -------------------------------------------------------------------------- *)
(* ----There exists an additive identity element  *)
(* ----Multiplicative zero  *)
(* ----Existence of left additive additive_inverse  *)
(* ----Inverse of additive_inverse of X is X  *)
(* ----Distributive property of product over sum  *)
(* ----Commutativity for addition  *)
(* ----Associativity for addition  *)
(* ----Right alternative law  *)
(* ----Left alternative law  *)
(* ----Associator  *)
(* ----Commutator  *)
(* -------------------------------------------------------------------------- *)
(* -------------------------------------------------------------------------- *)
(* ----The next 7 clause are extra lemmas which Stevens found useful  *)
theorem prove_right_alternative:
 \forall Univ:Set.
\forall add:\forall _:Univ.\forall _:Univ.Univ.
\forall additive_identity:Univ.
\forall additive_inverse:\forall _:Univ.Univ.
\forall associator:\forall _:Univ.\forall _:Univ.\forall _:Univ.Univ.
\forall commutator:\forall _:Univ.\forall _:Univ.Univ.
\forall multiply:\forall _:Univ.\forall _:Univ.Univ.
\forall x:Univ.
\forall y:Univ.
\forall H0:\forall X:Univ.\forall Y:Univ.\forall Z:Univ.eq Univ (multiply (add X Y) (additive_inverse Z)) (add (additive_inverse (multiply X Z)) (additive_inverse (multiply Y Z))).
\forall H1:\forall X:Univ.\forall Y:Univ.\forall Z:Univ.eq Univ (multiply (additive_inverse X) (add Y Z)) (add (additive_inverse (multiply X Y)) (additive_inverse (multiply X Z))).
\forall H2:\forall X:Univ.\forall Y:Univ.\forall Z:Univ.eq Univ (multiply (add X (additive_inverse Y)) Z) (add (multiply X Z) (additive_inverse (multiply Y Z))).
\forall H3:\forall X:Univ.\forall Y:Univ.\forall Z:Univ.eq Univ (multiply X (add Y (additive_inverse Z))) (add (multiply X Y) (additive_inverse (multiply X Z))).
\forall H4:\forall X:Univ.\forall Y:Univ.eq Univ (multiply X (additive_inverse Y)) (additive_inverse (multiply X Y)).
\forall H5:\forall X:Univ.\forall Y:Univ.eq Univ (multiply (additive_inverse X) Y) (additive_inverse (multiply X Y)).
\forall H6:\forall X:Univ.\forall Y:Univ.eq Univ (multiply (additive_inverse X) (additive_inverse Y)) (multiply X Y).
\forall H7:\forall X:Univ.\forall Y:Univ.eq Univ (commutator X Y) (add (multiply Y X) (additive_inverse (multiply X Y))).
\forall H8:\forall X:Univ.\forall Y:Univ.\forall Z:Univ.eq Univ (associator X Y Z) (add (multiply (multiply X Y) Z) (additive_inverse (multiply X (multiply Y Z)))).
\forall H9:\forall X:Univ.\forall Y:Univ.eq Univ (multiply (multiply X X) Y) (multiply X (multiply X Y)).
\forall H10:\forall X:Univ.\forall Y:Univ.eq Univ (multiply (multiply X Y) Y) (multiply X (multiply Y Y)).
\forall H11:\forall X:Univ.\forall Y:Univ.\forall Z:Univ.eq Univ (add X (add Y Z)) (add (add X Y) Z).
\forall H12:\forall X:Univ.\forall Y:Univ.eq Univ (add X Y) (add Y X).
\forall H13:\forall X:Univ.\forall Y:Univ.\forall Z:Univ.eq Univ (multiply (add X Y) Z) (add (multiply X Z) (multiply Y Z)).
\forall H14:\forall X:Univ.\forall Y:Univ.\forall Z:Univ.eq Univ (multiply X (add Y Z)) (add (multiply X Y) (multiply X Z)).
\forall H15:\forall X:Univ.eq Univ (additive_inverse (additive_inverse X)) X.
\forall H16:\forall X:Univ.eq Univ (add X (additive_inverse X)) additive_identity.
\forall H17:\forall X:Univ.eq Univ (add (additive_inverse X) X) additive_identity.
\forall H18:\forall X:Univ.eq Univ (multiply X additive_identity) additive_identity.
\forall H19:\forall X:Univ.eq Univ (multiply additive_identity X) additive_identity.
\forall H20:\forall X:Univ.eq Univ (add X additive_identity) X.
\forall H21:\forall X:Univ.eq Univ (add additive_identity X) X.eq Univ (associator x y y) additive_identity
.
intros.
autobatch paramodulation timeout=100;
try assumption.
print proofterm.
qed.
(* -------------------------------------------------------------------------- *)

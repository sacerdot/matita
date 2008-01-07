
include "logic/equality.ma".
(* Inclusion of: RNG007-4.p *)
(* -------------------------------------------------------------------------- *)
(*  File     : RNG007-4 : TPTP v3.1.1. Released v1.0.0. *)
(*  Domain   : Ring Theory *)
(*  Problem  : In Boolean rings, X is its own inverse *)
(*  Version  : [Peterson & Stickel, 1981] (equality) axioms. *)
(*             Theorem formulation : Equality. *)
(*  English  : Given a ring in which for all x, x * x = x, prove that for  *)
(*             all x, x + x = additive_identity *)
(*  Refs     : [PS81]  Peterson & Stickel (1981), Complete Sets of Reductions *)
(*  Source   : [ANL] *)
(*  Names    : lemma.ver2.in [ANL] *)
(*  Status   : Unsatisfiable *)
(*  Rating   : 0.00 v2.2.1, 0.11 v2.2.0, 0.14 v2.1.0, 0.13 v2.0.0 *)
(*  Syntax   : Number of clauses     :   16 (   0 non-Horn;  16 unit;   2 RR) *)
(*             Number of atoms       :   16 (  16 equality) *)
(*             Maximal clause size   :    1 (   1 average) *)
(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)
(*             Number of functors    :    5 (   2 constant; 0-2 arity) *)
(*             Number of variables   :   26 (   2 singleton) *)
(*             Maximal term depth    :    3 (   2 average) *)
(*  Comments :  *)
(* -------------------------------------------------------------------------- *)
(* ----Include ring theory axioms  *)
(* Inclusion of: Axioms/RNG002-0.ax *)
(* -------------------------------------------------------------------------- *)
(*  File     : RNG002-0 : TPTP v3.1.1. Released v1.0.0. *)
(*  Domain   : Ring Theory *)
(*  Axioms   : Ring theory (equality) axioms *)
(*  Version  : [PS81] (equality) axioms : *)
(*             Reduced & Augmented > Complete. *)
(*  English  :  *)
(*  Refs     : [PS81]  Peterson & Stickel (1981), Complete Sets of Reductions *)
(*  Source   : [ANL] *)
(*  Names    :  *)
(*  Status   :  *)
(*  Syntax   : Number of clauses    :   14 (   0 non-Horn;  14 unit;   1 RR) *)
(*             Number of literals   :   14 (  14 equality) *)
(*             Maximal clause size  :    1 (   1 average) *)
(*             Number of predicates :    1 (   0 propositional; 2-2 arity) *)
(*             Number of functors   :    4 (   1 constant; 0-2 arity) *)
(*             Number of variables  :   25 (   2 singleton) *)
(*             Maximal term depth   :    3 (   2 average) *)
(*  Comments : Not sure if these are complete. I don't know if the reductions *)
(*             given in [PS81] are suitable for ATP. *)
(* -------------------------------------------------------------------------- *)
(* ----Existence of left identity for addition  *)
(* ----Existence of left additive additive_inverse  *)
(* ----Distributive property of product over sum  *)
(* ----Inverse of identity is identity, stupid  *)
(* ----Inverse of additive_inverse of X is X  *)
(* ----Behavior of 0 and the multiplication operation  *)
(* ----Inverse of (x + y) is additive_inverse(x) + additive_inverse(y)  *)
(* ----x * additive_inverse(y) = additive_inverse (x * y)  *)
(* ----Associativity of addition  *)
(* ----Commutativity of addition  *)
(* ----Associativity of product  *)
(* -------------------------------------------------------------------------- *)
(* -------------------------------------------------------------------------- *)
theorem prove_inverse:
 \forall Univ:Set.
\forall a:Univ.
\forall add:\forall _:Univ.\forall _:Univ.Univ.
\forall additive_identity:Univ.
\forall additive_inverse:\forall _:Univ.Univ.
\forall multiply:\forall _:Univ.\forall _:Univ.Univ.
\forall H0:\forall X:Univ.eq Univ (multiply X X) X.
\forall H1:\forall X:Univ.\forall Y:Univ.\forall Z:Univ.eq Univ (multiply (multiply X Y) Z) (multiply X (multiply Y Z)).
\forall H2:\forall X:Univ.\forall Y:Univ.eq Univ (add X Y) (add Y X).
\forall H3:\forall X:Univ.\forall Y:Univ.\forall Z:Univ.eq Univ (add (add X Y) Z) (add X (add Y Z)).
\forall H4:\forall X:Univ.\forall Y:Univ.eq Univ (multiply (additive_inverse X) Y) (additive_inverse (multiply X Y)).
\forall H5:\forall X:Univ.\forall Y:Univ.eq Univ (multiply X (additive_inverse Y)) (additive_inverse (multiply X Y)).
\forall H6:\forall X:Univ.\forall Y:Univ.eq Univ (additive_inverse (add X Y)) (add (additive_inverse X) (additive_inverse Y)).
\forall H7:\forall X:Univ.eq Univ (multiply additive_identity X) additive_identity.
\forall H8:\forall X:Univ.eq Univ (multiply X additive_identity) additive_identity.
\forall H9:\forall X:Univ.eq Univ (additive_inverse (additive_inverse X)) X.
\forall H10:eq Univ (additive_inverse additive_identity) additive_identity.
\forall H11:\forall X:Univ.\forall Y:Univ.\forall Z:Univ.eq Univ (multiply (add X Y) Z) (add (multiply X Z) (multiply Y Z)).
\forall H12:\forall X:Univ.\forall Y:Univ.\forall Z:Univ.eq Univ (multiply X (add Y Z)) (add (multiply X Y) (multiply X Z)).
\forall H13:\forall X:Univ.eq Univ (add (additive_inverse X) X) additive_identity.
\forall H14:\forall X:Univ.eq Univ (add additive_identity X) X.eq Univ (add a a) additive_identity
.
intros.
autobatch paramodulation timeout=100;
try assumption.
print proofterm.
qed.
(* -------------------------------------------------------------------------- *)

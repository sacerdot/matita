
include "logic/equality.ma".
(* Inclusion of: RNG011-5.p *)
(* -------------------------------------------------------------------------- *)
(*  File     : RNG011-5 : TPTP v3.1.1. Released v1.0.0. *)
(*  Domain   : Ring Theory *)
(*  Problem  : In a right alternative ring (((X,X,Y)*X)*(X,X,Y)) = Add Id *)
(*  Version  : [Ove90] (equality) axioms : *)
(*             Incomplete > Augmented > Incomplete. *)
(*  English  :  *)
(*  Refs     : [Ove90] Overbeek (1990), ATP competition announced at CADE-10 *)
(*           : [Ove93] Overbeek (1993), The CADE-11 Competitions: A Personal  *)
(*           : [LM93]  Lusk & McCune (1993), Uniform Strategies: The CADE-11  *)
(*           : [Zha93] Zhang (1993), Automated Proofs of Equality Problems in *)
(*  Source   : [Ove90] *)
(*  Names    : CADE-11 Competition Eq-10 [Ove90] *)
(*           : THEOREM EQ-10 [LM93] *)
(*           : PROBLEM 10 [Zha93] *)
(*  Status   : Unsatisfiable *)
(*  Rating   : 0.00 v2.0.0 *)
(*  Syntax   : Number of clauses     :   22 (   0 non-Horn;  22 unit;   2 RR) *)
(*             Number of atoms       :   22 (  22 equality) *)
(*             Maximal clause size   :    1 (   1 average) *)
(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)
(*             Number of functors    :    8 (   3 constant; 0-3 arity) *)
(*             Number of variables   :   37 (   2 singleton) *)
(*             Maximal term depth    :    5 (   2 average) *)
(*  Comments :  *)
(* -------------------------------------------------------------------------- *)
(* ----Commutativity of addition  *)
(* ----Associativity of addition  *)
(* ----Additive identity  *)
(* ----Additive inverse  *)
(* ----Inverse of identity is identity, stupid  *)
(* ----Axiom of Overbeek  *)
(* ----Inverse of (x + y) is additive_inverse(x) + additive_inverse(y),  *)
(* ----Inverse of additive_inverse of X is X  *)
(* ----Behavior of 0 and the multiplication operation  *)
(* ----Axiom of Overbeek  *)
(* ----x * additive_inverse(y) = additive_inverse (x * y),  *)
(* ----Distributive property of product over sum  *)
(* ----Right alternative law  *)
(* ----Associator  *)
(* ----Commutator  *)
(* ----Middle associator identity  *)
theorem prove_equality:
 \forall Univ:Set.
\forall a:Univ.
\forall add:\forall _:Univ.\forall _:Univ.Univ.
\forall additive_identity:Univ.
\forall additive_inverse:\forall _:Univ.Univ.
\forall associator:\forall _:Univ.\forall _:Univ.\forall _:Univ.Univ.
\forall b:Univ.
\forall commutator:\forall _:Univ.\forall _:Univ.Univ.
\forall multiply:\forall _:Univ.\forall _:Univ.Univ.
\forall H0:\forall X:Univ.\forall Y:Univ.eq Univ (multiply (multiply (associator X X Y) X) (associator X X Y)) additive_identity.
\forall H1:\forall X:Univ.\forall Y:Univ.eq Univ (commutator X Y) (add (multiply Y X) (additive_inverse (multiply X Y))).
\forall H2:\forall X:Univ.\forall Y:Univ.\forall Z:Univ.eq Univ (associator X Y Z) (add (multiply (multiply X Y) Z) (additive_inverse (multiply X (multiply Y Z)))).
\forall H3:\forall X:Univ.\forall Y:Univ.eq Univ (multiply (multiply X Y) Y) (multiply X (multiply Y Y)).
\forall H4:\forall X:Univ.\forall Y:Univ.\forall Z:Univ.eq Univ (multiply (add X Y) Z) (add (multiply X Z) (multiply Y Z)).
\forall H5:\forall X:Univ.\forall Y:Univ.\forall Z:Univ.eq Univ (multiply X (add Y Z)) (add (multiply X Y) (multiply X Z)).
\forall H6:\forall X:Univ.\forall Y:Univ.eq Univ (multiply (additive_inverse X) Y) (additive_inverse (multiply X Y)).
\forall H7:\forall X:Univ.\forall Y:Univ.eq Univ (multiply X (additive_inverse Y)) (additive_inverse (multiply X Y)).
\forall H8:\forall X:Univ.\forall Y:Univ.eq Univ (multiply (additive_inverse X) (additive_inverse Y)) (multiply X Y).
\forall H9:\forall X:Univ.eq Univ (multiply additive_identity X) additive_identity.
\forall H10:\forall X:Univ.eq Univ (multiply X additive_identity) additive_identity.
\forall H11:\forall X:Univ.eq Univ (additive_inverse (additive_inverse X)) X.
\forall H12:\forall X:Univ.\forall Y:Univ.eq Univ (additive_inverse (add X Y)) (add (additive_inverse X) (additive_inverse Y)).
\forall H13:\forall X:Univ.\forall Y:Univ.eq Univ (add X (add (additive_inverse X) Y)) Y.
\forall H14:eq Univ (additive_inverse additive_identity) additive_identity.
\forall H15:\forall X:Univ.eq Univ (add (additive_inverse X) X) additive_identity.
\forall H16:\forall X:Univ.eq Univ (add X (additive_inverse X)) additive_identity.
\forall H17:\forall X:Univ.eq Univ (add additive_identity X) X.
\forall H18:\forall X:Univ.eq Univ (add X additive_identity) X.
\forall H19:\forall X:Univ.\forall Y:Univ.\forall Z:Univ.eq Univ (add (add X Y) Z) (add X (add Y Z)).
\forall H20:\forall X:Univ.\forall Y:Univ.eq Univ (add X Y) (add Y X).eq Univ (multiply (multiply (associator a a b) a) (associator a a b)) additive_identity
.
intros.
autobatch paramodulation timeout=100;
try assumption.
print proofterm.
qed.
(* -------------------------------------------------------------------------- *)

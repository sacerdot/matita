include "logic/equality.ma".

(* Inclusion of: RNG011-5.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : RNG011-5 : TPTP v3.7.0. Released v1.0.0. *)

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
ntheorem prove_equality:
 (∀Univ:Type.∀X:Univ.∀Y:Univ.∀Z:Univ.
∀a:Univ.
∀add:∀_:Univ.∀_:Univ.Univ.
∀additive_identity:Univ.
∀additive_inverse:∀_:Univ.Univ.
∀associator:∀_:Univ.∀_:Univ.∀_:Univ.Univ.
∀b:Univ.
∀commutator:∀_:Univ.∀_:Univ.Univ.
∀multiply:∀_:Univ.∀_:Univ.Univ.
∀H0:∀X:Univ.∀Y:Univ.eq Univ (multiply (multiply (associator X X Y) X) (associator X X Y)) additive_identity.
∀H1:∀X:Univ.∀Y:Univ.eq Univ (commutator X Y) (add (multiply Y X) (additive_inverse (multiply X Y))).
∀H2:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (associator X Y Z) (add (multiply (multiply X Y) Z) (additive_inverse (multiply X (multiply Y Z)))).
∀H3:∀X:Univ.∀Y:Univ.eq Univ (multiply (multiply X Y) Y) (multiply X (multiply Y Y)).
∀H4:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (multiply (add X Y) Z) (add (multiply X Z) (multiply Y Z)).
∀H5:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (multiply X (add Y Z)) (add (multiply X Y) (multiply X Z)).
∀H6:∀X:Univ.∀Y:Univ.eq Univ (multiply (additive_inverse X) Y) (additive_inverse (multiply X Y)).
∀H7:∀X:Univ.∀Y:Univ.eq Univ (multiply X (additive_inverse Y)) (additive_inverse (multiply X Y)).
∀H8:∀X:Univ.∀Y:Univ.eq Univ (multiply (additive_inverse X) (additive_inverse Y)) (multiply X Y).
∀H9:∀X:Univ.eq Univ (multiply additive_identity X) additive_identity.
∀H10:∀X:Univ.eq Univ (multiply X additive_identity) additive_identity.
∀H11:∀X:Univ.eq Univ (additive_inverse (additive_inverse X)) X.
∀H12:∀X:Univ.∀Y:Univ.eq Univ (additive_inverse (add X Y)) (add (additive_inverse X) (additive_inverse Y)).
∀H13:∀X:Univ.∀Y:Univ.eq Univ (add X (add (additive_inverse X) Y)) Y.
∀H14:eq Univ (additive_inverse additive_identity) additive_identity.
∀H15:∀X:Univ.eq Univ (add (additive_inverse X) X) additive_identity.
∀H16:∀X:Univ.eq Univ (add X (additive_inverse X)) additive_identity.
∀H17:∀X:Univ.eq Univ (add additive_identity X) X.
∀H18:∀X:Univ.eq Univ (add X additive_identity) X.
∀H19:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (add (add X Y) Z) (add X (add Y Z)).
∀H20:∀X:Univ.∀Y:Univ.eq Univ (add X Y) (add Y X).eq Univ (multiply (multiply (associator a a b) a) (associator a a b)) additive_identity)
.
#Univ ##.
#X ##.
#Y ##.
#Z ##.
#a ##.
#add ##.
#additive_identity ##.
#additive_inverse ##.
#associator ##.
#b ##.
#commutator ##.
#multiply ##.
#H0 ##.
#H1 ##.
#H2 ##.
#H3 ##.
#H4 ##.
#H5 ##.
#H6 ##.
#H7 ##.
#H8 ##.
#H9 ##.
#H10 ##.
#H11 ##.
#H12 ##.
#H13 ##.
#H14 ##.
#H15 ##.
#H16 ##.
#H17 ##.
#H18 ##.
#H19 ##.
#H20 ##.
nauto by H0,H1,H2,H3,H4,H5,H6,H7,H8,H9,H10,H11,H12,H13,H14,H15,H16,H17,H18,H19,H20 ##;
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)

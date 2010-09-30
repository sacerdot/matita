include "logic/equality.ma".

(* Inclusion of: RNG010-5.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : RNG010-5 : TPTP v3.7.0. Bugfixed v2.3.0. *)

(*  Domain   : Ring Theory (Right alternative) *)

(*  Problem  : Skew symmetry of the auxilliary function *)

(*  Version  : [Ove90] (equality) axioms : *)

(*             Incomplete > Augmented > Incomplete. *)

(*  English  : The three Moufang identities imply the skew symmetry  *)

(*             of s(W,X,Y,Z) = (W*X,Y,Z) - X*(W,Y,Z) - (X,Y,Z)*W. *)

(*             Recall that skew symmetry means that the function sign  *)

(*             changes when any two arguments are swapped. This problem  *)

(*             proves the case for swapping the first two arguments. *)

(*  Refs     : [Ove90] Overbeek (1990), ATP competition announced at CADE-10 *)

(*           : [Ove93] Overbeek (1993), The CADE-11 Competitions: A Personal  *)

(*           : [LM93]  Lusk & McCune (1993), Uniform Strategies: The CADE-11  *)

(*           : [Zha93] Zhang (1993), Automated Proofs of Equality Problems in *)

(*  Source   : [Ove90] *)

(*  Names    : CADE-11 Competition Eq-9 [Ove90] *)

(*           : THEOREM EQ-9 [LM93] *)

(*           : PROBLEM 9 [Zha93] *)

(*  Status   : Unknown *)

(*  Rating   : 1.00 v2.3.0 *)

(*  Syntax   : Number of clauses     :   27 (   0 non-Horn;  27 unit;   2 RR) *)

(*             Number of atoms       :   27 (  27 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :   11 (   5 constant; 0-4 arity) *)

(*             Number of variables   :   52 (   2 singleton) *)

(*             Maximal term depth    :    6 (   3 average) *)

(*  Comments : I copied this directly. I think the Moufang identities may  *)

(*             be wrong. At least they're in another form. *)

(*           : Yes, now they known to be wrong, and bugfixed in v2.3.0. *)

(*  Bugfixes : v2.3.0 - Clauses right_moufang and left_moufang fixed. *)

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

(* ----Left alternative law  *)

(* ----Definition of s  *)

(* ----Right Moufang  *)

(* ----Left Moufang  *)

(* ----Middle Moufang  *)
ntheorem prove_skew_symmetry:
 (∀Univ:Type.∀W:Univ.∀X:Univ.∀Y:Univ.∀Z:Univ.
∀a:Univ.
∀add:∀_:Univ.∀_:Univ.Univ.
∀additive_identity:Univ.
∀additive_inverse:∀_:Univ.Univ.
∀associator:∀_:Univ.∀_:Univ.∀_:Univ.Univ.
∀b:Univ.
∀c:Univ.
∀commutator:∀_:Univ.∀_:Univ.Univ.
∀d:Univ.
∀multiply:∀_:Univ.∀_:Univ.Univ.
∀s:∀_:Univ.∀_:Univ.∀_:Univ.∀_:Univ.Univ.
∀H0:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (multiply (multiply X Y) (multiply Z X)) (multiply (multiply X (multiply Y Z)) X).
∀H1:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (multiply (multiply X (multiply Y X)) Z) (multiply X (multiply Y (multiply X Z))).
∀H2:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (multiply Z (multiply X (multiply Y X))) (multiply (multiply (multiply Z X) Y) X).
∀H3:∀W:Univ.∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (s W X Y Z) (add (add (associator (multiply W X) Y Z) (additive_inverse (multiply X (associator W Y Z)))) (additive_inverse (multiply (associator X Y Z) W))).
∀H4:∀X:Univ.∀Y:Univ.eq Univ (multiply (multiply X X) Y) (multiply X (multiply X Y)).
∀H5:∀X:Univ.∀Y:Univ.eq Univ (multiply (multiply (associator X X Y) X) (associator X X Y)) additive_identity.
∀H6:∀X:Univ.∀Y:Univ.eq Univ (commutator X Y) (add (multiply Y X) (additive_inverse (multiply X Y))).
∀H7:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (associator X Y Z) (add (multiply (multiply X Y) Z) (additive_inverse (multiply X (multiply Y Z)))).
∀H8:∀X:Univ.∀Y:Univ.eq Univ (multiply (multiply X Y) Y) (multiply X (multiply Y Y)).
∀H9:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (multiply (add X Y) Z) (add (multiply X Z) (multiply Y Z)).
∀H10:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (multiply X (add Y Z)) (add (multiply X Y) (multiply X Z)).
∀H11:∀X:Univ.∀Y:Univ.eq Univ (multiply (additive_inverse X) Y) (additive_inverse (multiply X Y)).
∀H12:∀X:Univ.∀Y:Univ.eq Univ (multiply X (additive_inverse Y)) (additive_inverse (multiply X Y)).
∀H13:∀X:Univ.∀Y:Univ.eq Univ (multiply (additive_inverse X) (additive_inverse Y)) (multiply X Y).
∀H14:∀X:Univ.eq Univ (multiply additive_identity X) additive_identity.
∀H15:∀X:Univ.eq Univ (multiply X additive_identity) additive_identity.
∀H16:∀X:Univ.eq Univ (additive_inverse (additive_inverse X)) X.
∀H17:∀X:Univ.∀Y:Univ.eq Univ (additive_inverse (add X Y)) (add (additive_inverse X) (additive_inverse Y)).
∀H18:∀X:Univ.∀Y:Univ.eq Univ (add X (add (additive_inverse X) Y)) Y.
∀H19:eq Univ (additive_inverse additive_identity) additive_identity.
∀H20:∀X:Univ.eq Univ (add (additive_inverse X) X) additive_identity.
∀H21:∀X:Univ.eq Univ (add X (additive_inverse X)) additive_identity.
∀H22:∀X:Univ.eq Univ (add additive_identity X) X.
∀H23:∀X:Univ.eq Univ (add X additive_identity) X.
∀H24:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (add (add X Y) Z) (add X (add Y Z)).
∀H25:∀X:Univ.∀Y:Univ.eq Univ (add X Y) (add Y X).eq Univ (s a b c d) (additive_inverse (s b a c d)))
.
#Univ ##.
#W ##.
#X ##.
#Y ##.
#Z ##.
#a ##.
#add ##.
#additive_identity ##.
#additive_inverse ##.
#associator ##.
#b ##.
#c ##.
#commutator ##.
#d ##.
#multiply ##.
#s ##.
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
#H21 ##.
#H22 ##.
#H23 ##.
#H24 ##.
#H25 ##.
nauto by H0,H1,H2,H3,H4,H5,H6,H7,H8,H9,H10,H11,H12,H13,H14,H15,H16,H17,H18,H19,H20,H21,H22,H23,H24,H25 ##;
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)

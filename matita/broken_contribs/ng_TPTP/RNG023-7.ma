include "logic/equality.ma".

(* Inclusion of: RNG023-7.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : RNG023-7 : TPTP v3.7.0. Released v1.0.0. *)

(*  Domain   : Ring Theory (Alternative) *)

(*  Problem  : Left alternative *)

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

(*  File     : RNG003-0 : TPTP v3.7.0. Released v1.0.0. *)

(*  Domain   : Ring Theory (Alternative) *)

(*  Axioms   : Alternative ring theory (equality) axioms *)

(*  Version  : [Ste87] (equality) axioms. *)

(*  English  :  *)

(*  Refs     : [Ste87] Stevens (1987), Some Experiments in Nonassociative Rin *)

(*  Source   : [Ste87] *)

(*  Names    :  *)

(*  Status   :  *)

(*  Syntax   : Number of clauses    :   15 (   0 non-Horn;  15 unit;   0 RR) *)

(*             Number of atoms      :   15 (  15 equality) *)

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
ntheorem prove_left_alternative:
 (∀Univ:Type.∀X:Univ.∀Y:Univ.∀Z:Univ.
∀add:∀_:Univ.∀_:Univ.Univ.
∀additive_identity:Univ.
∀additive_inverse:∀_:Univ.Univ.
∀associator:∀_:Univ.∀_:Univ.∀_:Univ.Univ.
∀commutator:∀_:Univ.∀_:Univ.Univ.
∀multiply:∀_:Univ.∀_:Univ.Univ.
∀x:Univ.
∀y:Univ.
∀H0:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (multiply (add X Y) (additive_inverse Z)) (add (additive_inverse (multiply X Z)) (additive_inverse (multiply Y Z))).
∀H1:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (multiply (additive_inverse X) (add Y Z)) (add (additive_inverse (multiply X Y)) (additive_inverse (multiply X Z))).
∀H2:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (multiply (add X (additive_inverse Y)) Z) (add (multiply X Z) (additive_inverse (multiply Y Z))).
∀H3:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (multiply X (add Y (additive_inverse Z))) (add (multiply X Y) (additive_inverse (multiply X Z))).
∀H4:∀X:Univ.∀Y:Univ.eq Univ (multiply X (additive_inverse Y)) (additive_inverse (multiply X Y)).
∀H5:∀X:Univ.∀Y:Univ.eq Univ (multiply (additive_inverse X) Y) (additive_inverse (multiply X Y)).
∀H6:∀X:Univ.∀Y:Univ.eq Univ (multiply (additive_inverse X) (additive_inverse Y)) (multiply X Y).
∀H7:∀X:Univ.∀Y:Univ.eq Univ (commutator X Y) (add (multiply Y X) (additive_inverse (multiply X Y))).
∀H8:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (associator X Y Z) (add (multiply (multiply X Y) Z) (additive_inverse (multiply X (multiply Y Z)))).
∀H9:∀X:Univ.∀Y:Univ.eq Univ (multiply (multiply X X) Y) (multiply X (multiply X Y)).
∀H10:∀X:Univ.∀Y:Univ.eq Univ (multiply (multiply X Y) Y) (multiply X (multiply Y Y)).
∀H11:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (add X (add Y Z)) (add (add X Y) Z).
∀H12:∀X:Univ.∀Y:Univ.eq Univ (add X Y) (add Y X).
∀H13:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (multiply (add X Y) Z) (add (multiply X Z) (multiply Y Z)).
∀H14:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (multiply X (add Y Z)) (add (multiply X Y) (multiply X Z)).
∀H15:∀X:Univ.eq Univ (additive_inverse (additive_inverse X)) X.
∀H16:∀X:Univ.eq Univ (add X (additive_inverse X)) additive_identity.
∀H17:∀X:Univ.eq Univ (add (additive_inverse X) X) additive_identity.
∀H18:∀X:Univ.eq Univ (multiply X additive_identity) additive_identity.
∀H19:∀X:Univ.eq Univ (multiply additive_identity X) additive_identity.
∀H20:∀X:Univ.eq Univ (add X additive_identity) X.
∀H21:∀X:Univ.eq Univ (add additive_identity X) X.eq Univ (associator x x y) additive_identity)
.
#Univ ##.
#X ##.
#Y ##.
#Z ##.
#add ##.
#additive_identity ##.
#additive_inverse ##.
#associator ##.
#commutator ##.
#multiply ##.
#x ##.
#y ##.
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
nauto by H0,H1,H2,H3,H4,H5,H6,H7,H8,H9,H10,H11,H12,H13,H14,H15,H16,H17,H18,H19,H20,H21 ##;
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)

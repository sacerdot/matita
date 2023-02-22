include "logic/equality.ma".

(* Inclusion of: RNG027-5.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : RNG027-5 : TPTP v3.7.0. Released v1.0.0. *)

(*  Domain   : Ring Theory (Alternative) *)

(*  Problem  : Right Moufang identity *)

(*  Version  : [Ste87] (equality) axioms. *)

(*  English  :  *)

(*  Refs     : [Ste87] Stevens (1987), Some Experiments in Nonassociative Rin *)

(*           : [Ste88] Stevens (1988), Challenge Problems from Nonassociative *)

(*  Source   : [TPTP] *)

(*  Names    :  *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.78 v3.4.0, 0.75 v3.3.0, 0.86 v3.1.0, 0.89 v2.7.0, 0.91 v2.6.0, 0.83 v2.5.0, 0.75 v2.4.0, 0.67 v2.2.1, 1.00 v2.0.0 *)

(*  Syntax   : Number of clauses     :   16 (   0 non-Horn;  16 unit;   1 RR) *)

(*             Number of atoms       :   16 (  16 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    9 (   4 constant; 0-3 arity) *)

(*             Number of variables   :   27 (   2 singleton) *)

(*             Maximal term depth    :    5 (   2 average) *)

(*  Comments : [Ste88] presents a slightly different set of axioms for proving *)

(*             this ntheorem. The axioms are so similar to those in RNG004.ax *)

(*             that a separate problems has not been created. *)

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
ntheorem prove_right_moufang:
 (∀Univ:Type.∀X:Univ.∀Y:Univ.∀Z:Univ.
∀add:∀_:Univ.∀_:Univ.Univ.
∀additive_identity:Univ.
∀additive_inverse:∀_:Univ.Univ.
∀associator:∀_:Univ.∀_:Univ.∀_:Univ.Univ.
∀commutator:∀_:Univ.∀_:Univ.Univ.
∀cx:Univ.
∀cy:Univ.
∀cz:Univ.
∀multiply:∀_:Univ.∀_:Univ.Univ.
∀H0:∀X:Univ.∀Y:Univ.eq Univ (commutator X Y) (add (multiply Y X) (additive_inverse (multiply X Y))).
∀H1:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (associator X Y Z) (add (multiply (multiply X Y) Z) (additive_inverse (multiply X (multiply Y Z)))).
∀H2:∀X:Univ.∀Y:Univ.eq Univ (multiply (multiply X X) Y) (multiply X (multiply X Y)).
∀H3:∀X:Univ.∀Y:Univ.eq Univ (multiply (multiply X Y) Y) (multiply X (multiply Y Y)).
∀H4:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (add X (add Y Z)) (add (add X Y) Z).
∀H5:∀X:Univ.∀Y:Univ.eq Univ (add X Y) (add Y X).
∀H6:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (multiply (add X Y) Z) (add (multiply X Z) (multiply Y Z)).
∀H7:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (multiply X (add Y Z)) (add (multiply X Y) (multiply X Z)).
∀H8:∀X:Univ.eq Univ (additive_inverse (additive_inverse X)) X.
∀H9:∀X:Univ.eq Univ (add X (additive_inverse X)) additive_identity.
∀H10:∀X:Univ.eq Univ (add (additive_inverse X) X) additive_identity.
∀H11:∀X:Univ.eq Univ (multiply X additive_identity) additive_identity.
∀H12:∀X:Univ.eq Univ (multiply additive_identity X) additive_identity.
∀H13:∀X:Univ.eq Univ (add X additive_identity) X.
∀H14:∀X:Univ.eq Univ (add additive_identity X) X.eq Univ (multiply cz (multiply cx (multiply cy cx))) (multiply (multiply (multiply cz cx) cy) cx))
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
#cx ##.
#cy ##.
#cz ##.
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
nauto by H0,H1,H2,H3,H4,H5,H6,H7,H8,H9,H10,H11,H12,H13,H14 ##;
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)

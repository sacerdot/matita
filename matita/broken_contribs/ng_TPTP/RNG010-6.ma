include "logic/equality.ma".

(* Inclusion of: RNG010-6.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : RNG010-6 : TPTP v3.7.0. Bugfixed v2.3.0. *)

(*  Domain   : Ring Theory (Right alternative) *)

(*  Problem  : Skew symmetry of the auxilliary function *)

(*  Version  : [Ste87] (equality) axioms. *)

(*  English  : The three Moufang identities imply the skew symmetry  *)

(*             of s(W,X,Y,Z) = (W*X,Y,Z) - X*(W,Y,Z) - (X,Y,Z)*W. *)

(*             Recall that skew symmetry means that the function sign  *)

(*             changes when any two arguments are swapped. This problem  *)

(*             proves the case for swapping the first two arguments. *)

(*  Refs     : [Ste87] Stevens (1987), Some Experiments in Nonassociative Rin *)

(*  Source   : [TPTP] *)

(*  Names    :  *)

(*  Status   : Unknown *)

(*  Rating   : 1.00 v2.3.0 *)

(*  Syntax   : Number of clauses     :   20 (   0 non-Horn;  20 unit;   1 RR) *)

(*             Number of atoms       :   20 (  20 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :   11 (   5 constant; 0-4 arity) *)

(*             Number of variables   :   40 (   2 singleton) *)

(*             Maximal term depth    :    6 (   3 average) *)

(*  Comments :  *)

(*  Bugfixes : v2.3.0 - Clause prove_skew_symmetry fixed. *)

(*           : v2.3.0 - Left alternative law added in. *)

(*           : v2.3.0 - Clauses right_moufang and left_moufang fixed. *)

(* -------------------------------------------------------------------------- *)

(* ----Include nonassociative ring axioms. *)

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

(* ----Definition of s  *)

(* ----Right Moufang *)

(* ----Left Moufang *)
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
∀H4:∀X:Univ.∀Y:Univ.eq Univ (commutator X Y) (add (multiply Y X) (additive_inverse (multiply X Y))).
∀H5:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (associator X Y Z) (add (multiply (multiply X Y) Z) (additive_inverse (multiply X (multiply Y Z)))).
∀H6:∀X:Univ.∀Y:Univ.eq Univ (multiply (multiply X X) Y) (multiply X (multiply X Y)).
∀H7:∀X:Univ.∀Y:Univ.eq Univ (multiply (multiply X Y) Y) (multiply X (multiply Y Y)).
∀H8:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (add X (add Y Z)) (add (add X Y) Z).
∀H9:∀X:Univ.∀Y:Univ.eq Univ (add X Y) (add Y X).
∀H10:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (multiply (add X Y) Z) (add (multiply X Z) (multiply Y Z)).
∀H11:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (multiply X (add Y Z)) (add (multiply X Y) (multiply X Z)).
∀H12:∀X:Univ.eq Univ (additive_inverse (additive_inverse X)) X.
∀H13:∀X:Univ.eq Univ (add X (additive_inverse X)) additive_identity.
∀H14:∀X:Univ.eq Univ (add (additive_inverse X) X) additive_identity.
∀H15:∀X:Univ.eq Univ (multiply X additive_identity) additive_identity.
∀H16:∀X:Univ.eq Univ (multiply additive_identity X) additive_identity.
∀H17:∀X:Univ.eq Univ (add X additive_identity) X.
∀H18:∀X:Univ.eq Univ (add additive_identity X) X.eq Univ (s a b c d) (additive_inverse (s b a c d)))
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
nauto by H0,H1,H2,H3,H4,H5,H6,H7,H8,H9,H10,H11,H12,H13,H14,H15,H16,H17,H18 ##;
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)

include "logic/equality.ma".

(* Inclusion of: RNG033-9.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : RNG033-9 : TPTP v3.7.0. Bugfixed v2.3.0. *)

(*  Domain   : Ring Theory (Alternative) *)

(*  Problem  : A fairly complex equation with associators *)

(*  Version  : [Ste87] (equality) axioms : Augmented. *)

(*  English  : assr(X.Y,Z,W)+assr(X,Y,comm(Z,W)) = X.assr(Y,Z,W)+assr(X,Z,W).Y *)

(*  Refs     : [Ste87] Stevens (1987), Some Experiments in Nonassociative Rin *)

(*  Source   : [TPTP] *)

(*  Names    :  *)

(*  Status   : Unknown *)

(*  Rating   : 1.00 v2.3.0 *)

(*  Syntax   : Number of clauses     :   24 (   0 non-Horn;  24 unit;   1 RR) *)

(*             Number of atoms       :   24 (  24 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :   10 (   5 constant; 0-3 arity) *)

(*             Number of variables   :   48 (   2 singleton) *)

(*             Maximal term depth    :    5 (   3 average) *)

(*  Comments : This includes the right Moufang identity, which [Ste87]  *)

(*             suggests in a useful lemma for this problem. *)

(*  Bugfixes : v2.3.0 - Clause right_moufang fixed. *)

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

(* ----Right Moufang *)
ntheorem prove_challenge:
 (∀Univ:Type.∀X:Univ.∀Y:Univ.∀Z:Univ.
∀add:∀_:Univ.∀_:Univ.Univ.
∀additive_identity:Univ.
∀additive_inverse:∀_:Univ.Univ.
∀associator:∀_:Univ.∀_:Univ.∀_:Univ.Univ.
∀commutator:∀_:Univ.∀_:Univ.Univ.
∀multiply:∀_:Univ.∀_:Univ.Univ.
∀w:Univ.
∀x:Univ.
∀y:Univ.
∀z:Univ.
∀H0:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (multiply Z (multiply X (multiply Y X))) (multiply (multiply (multiply Z X) Y) X).
∀H1:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (multiply (add X Y) (additive_inverse Z)) (add (additive_inverse (multiply X Z)) (additive_inverse (multiply Y Z))).
∀H2:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (multiply (additive_inverse X) (add Y Z)) (add (additive_inverse (multiply X Y)) (additive_inverse (multiply X Z))).
∀H3:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (multiply (add X (additive_inverse Y)) Z) (add (multiply X Z) (additive_inverse (multiply Y Z))).
∀H4:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (multiply X (add Y (additive_inverse Z))) (add (multiply X Y) (additive_inverse (multiply X Z))).
∀H5:∀X:Univ.∀Y:Univ.eq Univ (multiply X (additive_inverse Y)) (additive_inverse (multiply X Y)).
∀H6:∀X:Univ.∀Y:Univ.eq Univ (multiply (additive_inverse X) Y) (additive_inverse (multiply X Y)).
∀H7:∀X:Univ.∀Y:Univ.eq Univ (multiply (additive_inverse X) (additive_inverse Y)) (multiply X Y).
∀H8:∀X:Univ.∀Y:Univ.eq Univ (commutator X Y) (add (multiply Y X) (additive_inverse (multiply X Y))).
∀H9:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (associator X Y Z) (add (multiply (multiply X Y) Z) (additive_inverse (multiply X (multiply Y Z)))).
∀H10:∀X:Univ.∀Y:Univ.eq Univ (multiply (multiply X X) Y) (multiply X (multiply X Y)).
∀H11:∀X:Univ.∀Y:Univ.eq Univ (multiply (multiply X Y) Y) (multiply X (multiply Y Y)).
∀H12:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (add X (add Y Z)) (add (add X Y) Z).
∀H13:∀X:Univ.∀Y:Univ.eq Univ (add X Y) (add Y X).
∀H14:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (multiply (add X Y) Z) (add (multiply X Z) (multiply Y Z)).
∀H15:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (multiply X (add Y Z)) (add (multiply X Y) (multiply X Z)).
∀H16:∀X:Univ.eq Univ (additive_inverse (additive_inverse X)) X.
∀H17:∀X:Univ.eq Univ (add X (additive_inverse X)) additive_identity.
∀H18:∀X:Univ.eq Univ (add (additive_inverse X) X) additive_identity.
∀H19:∀X:Univ.eq Univ (multiply X additive_identity) additive_identity.
∀H20:∀X:Univ.eq Univ (multiply additive_identity X) additive_identity.
∀H21:∀X:Univ.eq Univ (add X additive_identity) X.
∀H22:∀X:Univ.eq Univ (add additive_identity X) X.eq Univ (add (associator (multiply x y) z w) (associator x y (commutator z w))) (add (multiply x (associator y z w)) (multiply (associator x z w) y)))
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
#w ##.
#x ##.
#y ##.
#z ##.
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
nauto by H0,H1,H2,H3,H4,H5,H6,H7,H8,H9,H10,H11,H12,H13,H14,H15,H16,H17,H18,H19,H20,H21,H22 ##;
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)

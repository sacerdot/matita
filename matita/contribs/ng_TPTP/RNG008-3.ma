include "logic/equality.ma".

(* Inclusion of: RNG008-3.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : RNG008-3 : TPTP v3.7.0. Released v1.0.0. *)

(*  Domain   : Ring Theory *)

(*  Problem  : Boolean rings are commutative *)

(*  Version  : [PS81] (equality) axioms : Augmented. *)

(*             Theorem formulation : Equality. *)

(*  English  : Given a ring in which for all x, x * x = x, prove that for  *)

(*             all x and y, x * y = y * x. *)

(*  Refs     : [MOW76] McCharen et al. (1976), Problems and Experiments for a *)

(*           : [PS81]  Peterson & Stickel (1981), Complete Sets of Reductions *)

(*  Source   : [ANL] *)

(*  Names    : commute.ver2.in [ANL] *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.00 v3.3.0, 0.07 v3.1.0, 0.11 v2.7.0, 0.00 v2.2.1, 0.22 v2.2.0, 0.29 v2.1.0, 0.25 v2.0.0 *)

(*  Syntax   : Number of clauses     :   19 (   0 non-Horn;  19 unit;   3 RR) *)

(*             Number of atoms       :   19 (  19 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    7 (   4 constant; 0-2 arity) *)

(*             Number of variables   :   28 (   2 singleton) *)

(*             Maximal term depth    :    3 (   2 average) *)

(*  Comments :  *)

(* -------------------------------------------------------------------------- *)

(* ----Include ring theory axioms  *)

(* Inclusion of: Axioms/RNG002-0.ax *)

(* -------------------------------------------------------------------------- *)

(*  File     : RNG002-0 : TPTP v3.7.0. Released v1.0.0. *)

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

(*             Number of atoms      :   14 (  14 equality) *)

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

(* ----Right identity and inverse are dependent lemmas  *)
ntheorem prove_commutativity:
 (∀Univ:Type.∀X:Univ.∀Y:Univ.∀Z:Univ.
∀a:Univ.
∀add:∀_:Univ.∀_:Univ.Univ.
∀additive_identity:Univ.
∀additive_inverse:∀_:Univ.Univ.
∀b:Univ.
∀c:Univ.
∀multiply:∀_:Univ.∀_:Univ.Univ.
∀H0:eq Univ (multiply a b) c.
∀H1:∀X:Univ.eq Univ (multiply X X) X.
∀H2:∀X:Univ.eq Univ (add X (additive_inverse X)) additive_identity.
∀H3:∀X:Univ.eq Univ (add X additive_identity) X.
∀H4:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (multiply (multiply X Y) Z) (multiply X (multiply Y Z)).
∀H5:∀X:Univ.∀Y:Univ.eq Univ (add X Y) (add Y X).
∀H6:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (add (add X Y) Z) (add X (add Y Z)).
∀H7:∀X:Univ.∀Y:Univ.eq Univ (multiply (additive_inverse X) Y) (additive_inverse (multiply X Y)).
∀H8:∀X:Univ.∀Y:Univ.eq Univ (multiply X (additive_inverse Y)) (additive_inverse (multiply X Y)).
∀H9:∀X:Univ.∀Y:Univ.eq Univ (additive_inverse (add X Y)) (add (additive_inverse X) (additive_inverse Y)).
∀H10:∀X:Univ.eq Univ (multiply additive_identity X) additive_identity.
∀H11:∀X:Univ.eq Univ (multiply X additive_identity) additive_identity.
∀H12:∀X:Univ.eq Univ (additive_inverse (additive_inverse X)) X.
∀H13:eq Univ (additive_inverse additive_identity) additive_identity.
∀H14:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (multiply (add X Y) Z) (add (multiply X Z) (multiply Y Z)).
∀H15:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (multiply X (add Y Z)) (add (multiply X Y) (multiply X Z)).
∀H16:∀X:Univ.eq Univ (add (additive_inverse X) X) additive_identity.
∀H17:∀X:Univ.eq Univ (add additive_identity X) X.eq Univ (multiply b a) c)
.
#Univ ##.
#X ##.
#Y ##.
#Z ##.
#a ##.
#add ##.
#additive_identity ##.
#additive_inverse ##.
#b ##.
#c ##.
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
nauto by H0,H1,H2,H3,H4,H5,H6,H7,H8,H9,H10,H11,H12,H13,H14,H15,H16,H17 ##;
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)

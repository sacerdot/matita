include "logic/equality.ma".

(* Inclusion of: RNG025-8.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : RNG025-8 : TPTP v3.7.0. Released v1.0.0. *)

(*  Domain   : Ring Theory (Alternative) *)

(*  Problem  : Middle or Flexible Law *)

(*  Version  : [Ste87] (equality) axioms : Reduced & Augmented > Complete. *)

(*             Theorem formulation : Linearized. *)

(*  English  :  *)

(*  Refs     : [Ste87] Stevens (1987), Some Experiments in Nonassociative Rin *)

(*  Source   : [TPTP] *)

(*  Names    :  *)

(*  Status   : Satisfiable *)

(*  Rating   : 0.33 v3.2.0, 0.67 v3.1.0, 0.33 v2.4.0, 0.67 v2.2.1, 0.75 v2.2.0, 0.67 v2.1.0, 1.00 v2.0.0 *)

(*  Syntax   : Number of clauses     :   18 (   0 non-Horn;  18 unit;   1 RR) *)

(*             Number of atoms       :   18 (  18 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    9 (   4 constant; 0-3 arity) *)

(*             Number of variables   :   36 (   2 singleton) *)

(*             Maximal term depth    :    4 (   2 average) *)

(*  Comments :  *)

(* -------------------------------------------------------------------------- *)

(* ----Don't Include nonassociative ring axioms. *)

(* ----The associator has to be replaced by its linearised form.  *)

(*  include('axioms/RNG003-0.ax'). *)

(* -------------------------------------------------------------------------- *)

(* ----Commutativity for addition  *)

(* ----Associativity for addition  *)

(* ----There exists an additive identity element  *)

(* ----Multiplicative zero  *)

(* ----Existence of left additive additive_inverse  *)

(* ----Distributive property of product over sum  *)

(* ----Inverse of additive_inverse of X is X  *)

(* ----Right alternative law  *)

(* ----Left alternative law  *)

(* ----Associator  *)

(*  input_clause(associator,axiom, *)

(*      [++equal(associator(X,Y,Z),add(multiply(multiply(X,Y),Z), *)

(*  additive_inverse(multiply(X,multiply(Y,Z)))))]). *)

(* ----Linearised for of the associator  *)

(* ----Commutator  *)
ntheorem prove_flexible_law:
 (∀Univ:Type.∀U:Univ.∀V:Univ.∀X:Univ.∀Y:Univ.∀Z:Univ.
∀a:Univ.
∀add:∀_:Univ.∀_:Univ.Univ.
∀additive_identity:Univ.
∀additive_inverse:∀_:Univ.Univ.
∀associator:∀_:Univ.∀_:Univ.∀_:Univ.Univ.
∀b:Univ.
∀c:Univ.
∀commutator:∀_:Univ.∀_:Univ.Univ.
∀multiply:∀_:Univ.∀_:Univ.Univ.
∀H0:∀X:Univ.∀Y:Univ.eq Univ (commutator X Y) (add (multiply Y X) (additive_inverse (multiply X Y))).
∀H1:∀U:Univ.∀V:Univ.∀X:Univ.∀Y:Univ.eq Univ (associator (add U V) X Y) (add (associator U X Y) (associator V X Y)).
∀H2:∀U:Univ.∀V:Univ.∀X:Univ.∀Y:Univ.eq Univ (associator X (add U V) Y) (add (associator X U Y) (associator X V Y)).
∀H3:∀U:Univ.∀V:Univ.∀X:Univ.∀Y:Univ.eq Univ (associator X Y (add U V)) (add (associator X Y U) (associator X Y V)).
∀H4:∀X:Univ.∀Y:Univ.eq Univ (multiply (multiply X X) Y) (multiply X (multiply X Y)).
∀H5:∀X:Univ.∀Y:Univ.eq Univ (multiply (multiply X Y) Y) (multiply X (multiply Y Y)).
∀H6:∀X:Univ.eq Univ (additive_inverse (additive_inverse X)) X.
∀H7:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (multiply (add X Y) Z) (add (multiply X Z) (multiply Y Z)).
∀H8:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (multiply X (add Y Z)) (add (multiply X Y) (multiply X Z)).
∀H9:∀X:Univ.eq Univ (add X (additive_inverse X)) additive_identity.
∀H10:∀X:Univ.eq Univ (add (additive_inverse X) X) additive_identity.
∀H11:∀X:Univ.eq Univ (multiply X additive_identity) additive_identity.
∀H12:∀X:Univ.eq Univ (multiply additive_identity X) additive_identity.
∀H13:∀X:Univ.eq Univ (add X additive_identity) X.
∀H14:∀X:Univ.eq Univ (add additive_identity X) X.
∀H15:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (add X (add Y Z)) (add (add X Y) Z).
∀H16:∀X:Univ.∀Y:Univ.eq Univ (add X Y) (add Y X).eq Univ (add (associator a b c) (associator a c b)) additive_identity)
.
#Univ ##.
#U ##.
#V ##.
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
nauto by H0,H1,H2,H3,H4,H5,H6,H7,H8,H9,H10,H11,H12,H13,H14,H15,H16 ##;
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)

include "logic/equality.ma".

(* Inclusion of: RNG032-6.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : RNG032-6 : TPTP v3.7.0. Released v1.0.0. *)

(*  Domain   : Ring Theory (Right alternative) *)

(*  Problem  : 6*assr(X,X,Y)^6 = additive identity *)

(*  Version  : [Ste87] (equality) axioms : Reduced > Complete. *)

(*  English  :  *)

(*  Refs     : [Ste87] Stevens (1987), Some Experiments in Nonassociative Rin *)

(*           : [Oto07] Otop (2007), Solution to some Right Alternative Ring P *)

(*  Source   : [Ste87] *)

(*  Names    : Conjecture 3 [Ste87] *)

(*  Status   : Satisfiable *)

(*  Rating   : 1.00 v2.0.0 *)

(*  Syntax   : Number of clauses     :   15 (   0 non-Horn;  15 unit;   1 RR) *)

(*             Number of atoms       :   15 (  15 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    8 (   3 constant; 0-3 arity) *)

(*             Number of variables   :   25 (   2 singleton) *)

(*             Maximal term depth    :    9 (   2 average) *)

(*  Comments :  *)

(* -------------------------------------------------------------------------- *)

(* ----Don't Include nonassociative ring axioms. *)

(* ----The left alternative law has to be omitted. *)

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

(*  input_clause(left_alternative,axiom, *)

(*      [++equal(multiply(multiply(X,X),Y),multiply(X,multiply(X,Y)))]). *)

(* ----Associator  *)

(* ----Commutator  *)
ntheorem prove_conjecture_3:
 (∀Univ:Type.∀X:Univ.∀Y:Univ.∀Z:Univ.
∀add:∀_:Univ.∀_:Univ.Univ.
∀additive_identity:Univ.
∀additive_inverse:∀_:Univ.Univ.
∀associator:∀_:Univ.∀_:Univ.∀_:Univ.Univ.
∀commutator:∀_:Univ.∀_:Univ.Univ.
∀multiply:∀_:Univ.∀_:Univ.Univ.
∀x:Univ.
∀y:Univ.
∀H0:∀X:Univ.∀Y:Univ.eq Univ (commutator X Y) (add (multiply Y X) (additive_inverse (multiply X Y))).
∀H1:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (associator X Y Z) (add (multiply (multiply X Y) Z) (additive_inverse (multiply X (multiply Y Z)))).
∀H2:∀X:Univ.∀Y:Univ.eq Univ (multiply (multiply X Y) Y) (multiply X (multiply Y Y)).
∀H3:∀X:Univ.eq Univ (additive_inverse (additive_inverse X)) X.
∀H4:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (multiply (add X Y) Z) (add (multiply X Z) (multiply Y Z)).
∀H5:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (multiply X (add Y Z)) (add (multiply X Y) (multiply X Z)).
∀H6:∀X:Univ.eq Univ (add X (additive_inverse X)) additive_identity.
∀H7:∀X:Univ.eq Univ (add (additive_inverse X) X) additive_identity.
∀H8:∀X:Univ.eq Univ (multiply X additive_identity) additive_identity.
∀H9:∀X:Univ.eq Univ (multiply additive_identity X) additive_identity.
∀H10:∀X:Univ.eq Univ (add X additive_identity) X.
∀H11:∀X:Univ.eq Univ (add additive_identity X) X.
∀H12:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (add X (add Y Z)) (add (add X Y) Z).
∀H13:∀X:Univ.∀Y:Univ.eq Univ (add X Y) (add Y X).eq Univ (add (add (add (add (add (multiply (associator x x y) (multiply (associator x x y) (associator x x y))) (multiply (associator x x y) (multiply (associator x x y) (associator x x y)))) (multiply (associator x x y) (multiply (associator x x y) (associator x x y)))) (multiply (associator x x y) (multiply (associator x x y) (associator x x y)))) (multiply (associator x x y) (multiply (associator x x y) (associator x x y)))) (multiply (associator x x y) (multiply (associator x x y) (associator x x y)))) additive_identity)
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
nauto by H0,H1,H2,H3,H4,H5,H6,H7,H8,H9,H10,H11,H12,H13 ##;
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)

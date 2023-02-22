include "logic/equality.ma".

(* Inclusion of: RNG036-7.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : RNG036-7 : TPTP v3.7.0. Released v1.0.0. *)

(*  Domain   : Ring Theory *)

(*  Problem  : If X*X*X*X*X = X then the ring is commutative *)

(*  Version  : [LW91] (equality) axioms. *)

(*  English  : Given a ring in which for all x, x * x * x * x * x = x, prove  *)

(*             that for all x and y, x * y = y * x. *)

(*  Refs     : [LW91]  Lusk & Wos (1991), Benchmark Problems in Which Equalit *)

(*  Source   : [LW91] *)

(*  Names    : RT4 [LW91] *)

(*  Status   : Unknown *)

(*  Rating   : 1.00 v2.0.0 *)

(*  Syntax   : Number of clauses     :   12 (   0 non-Horn;  12 unit;   2 RR) *)

(*             Number of atoms       :   12 (  12 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    7 (   4 constant; 0-2 arity) *)

(*             Number of variables   :   19 (   0 singleton) *)

(*             Maximal term depth    :    5 (   2 average) *)

(*  Comments :  *)

(* -------------------------------------------------------------------------- *)

(* ----Include ring theory axioms  *)

(* Inclusion of: Axioms/RNG005-0.ax *)

(* -------------------------------------------------------------------------- *)

(*  File     : RNG005-0 : TPTP v3.7.0. Released v1.0.0. *)

(*  Domain   : Ring Theory  *)

(*  Axioms   : Ring theory (equality) axioms *)

(*  Version  : [LW92] (equality) axioms. *)

(*  English  :  *)

(*  Refs     : [Wos88] Wos (1988), Automated Reasoning - 33 Basic Research Pr *)

(*           : [LW92]  Lusk & Wos (1992), Benchmark Problems in Which Equalit *)

(*  Source   : [LW92] *)

(*  Names    :  *)

(*  Status   :  *)

(*  Syntax   : Number of clauses    :    9 (   0 non-Horn;   9 unit;   0 RR) *)

(*             Number of atoms      :    9 (   9 equality) *)

(*             Maximal clause size  :    1 (   1 average) *)

(*             Number of predicates :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors   :    4 (   1 constant; 0-2 arity) *)

(*             Number of variables  :   18 (   0 singleton) *)

(*             Maximal term depth   :    3 (   2 average) *)

(*  Comments : These axioms are used in [Wos88] p.203. *)

(* -------------------------------------------------------------------------- *)

(* ----There exists an additive identity element  *)

(* ----Existence of left additive additive_inverse  *)

(* ----Associativity for addition  *)

(* ----Commutativity for addition  *)

(* ----Associativity for multiplication  *)

(* ----Distributive property of product over sum  *)

(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
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
∀H1:∀X:Univ.eq Univ (multiply X (multiply X (multiply X (multiply X X)))) X.
∀H2:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (multiply (add X Y) Z) (add (multiply X Z) (multiply Y Z)).
∀H3:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (multiply X (add Y Z)) (add (multiply X Y) (multiply X Z)).
∀H4:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (multiply X (multiply Y Z)) (multiply (multiply X Y) Z).
∀H5:∀X:Univ.∀Y:Univ.eq Univ (add X Y) (add Y X).
∀H6:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (add X (add Y Z)) (add (add X Y) Z).
∀H7:∀X:Univ.eq Univ (add X (additive_inverse X)) additive_identity.
∀H8:∀X:Univ.eq Univ (add (additive_inverse X) X) additive_identity.
∀H9:∀X:Univ.eq Univ (add X additive_identity) X.
∀H10:∀X:Univ.eq Univ (add additive_identity X) X.eq Univ (multiply b a) c)
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
nauto by H0,H1,H2,H3,H4,H5,H6,H7,H8,H9,H10 ##;
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)

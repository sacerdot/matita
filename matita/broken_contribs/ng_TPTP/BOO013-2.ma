include "logic/equality.ma".

(* Inclusion of: BOO013-2.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : BOO013-2 : TPTP v3.7.0. Bugfixed v1.2.1. *)

(*  Domain   : Boolean Algebra *)

(*  Problem  : The inverse of X is unique *)

(*  Version  : [ANL] (equality) axioms. *)

(*  English  :  *)

(*  Refs     :  *)

(*  Source   : [ANL] *)

(*  Names    : prob9.ver2.in [ANL] *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.00 v2.2.1, 0.11 v2.2.0, 0.14 v2.1.0, 0.14 v2.0.0 *)

(*  Syntax   : Number of clauses     :   19 (   0 non-Horn;  19 unit;   5 RR) *)

(*             Number of atoms       :   19 (  19 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    8 (   5 constant; 0-2 arity) *)

(*             Number of variables   :   24 (   0 singleton) *)

(*             Maximal term depth    :    3 (   2 average) *)

(*  Comments :  *)

(*  Bugfixes : v1.2.1 - Clauses b_and_multiplicative_identity and *)

(*             c_and_multiplicative_identity fixed. *)

(* -------------------------------------------------------------------------- *)

(* ----Include boolean algebra axioms for equality formulation  *)

(* Inclusion of: Axioms/BOO003-0.ax *)

(* -------------------------------------------------------------------------- *)

(*  File     : BOO003-0 : TPTP v3.7.0. Released v1.0.0. *)

(*  Domain   : Boolean Algebra *)

(*  Axioms   : Boolean algebra (equality) axioms *)

(*  Version  : [ANL] (equality) axioms. *)

(*  English  :  *)

(*  Refs     :  *)

(*  Source   : [ANL] *)

(*  Names    :  *)

(*  Status   :  *)

(*  Syntax   : Number of clauses    :   14 (   0 non-Horn;  14 unit;   0 RR) *)

(*             Number of atoms      :   14 (  14 equality) *)

(*             Maximal clause size  :    1 (   1 average) *)

(*             Number of predicates :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors   :    5 (   2 constant; 0-2 arity) *)

(*             Number of variables  :   24 (   0 singleton) *)

(*             Maximal term depth   :    3 (   2 average) *)

(*  Comments :  *)

(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
ntheorem prove_b_is_a:
 (∀Univ:Type.∀X:Univ.∀Y:Univ.∀Z:Univ.
∀a:Univ.
∀add:∀_:Univ.∀_:Univ.Univ.
∀additive_identity:Univ.
∀b:Univ.
∀c:Univ.
∀inverse:∀_:Univ.Univ.
∀multiplicative_identity:Univ.
∀multiply:∀_:Univ.∀_:Univ.Univ.
∀H0:eq Univ (multiply a c) additive_identity.
∀H1:eq Univ (multiply a b) additive_identity.
∀H2:eq Univ (add a c) multiplicative_identity.
∀H3:eq Univ (add a b) multiplicative_identity.
∀H4:∀X:Univ.eq Univ (add additive_identity X) X.
∀H5:∀X:Univ.eq Univ (add X additive_identity) X.
∀H6:∀X:Univ.eq Univ (multiply multiplicative_identity X) X.
∀H7:∀X:Univ.eq Univ (multiply X multiplicative_identity) X.
∀H8:∀X:Univ.eq Univ (multiply (inverse X) X) additive_identity.
∀H9:∀X:Univ.eq Univ (multiply X (inverse X)) additive_identity.
∀H10:∀X:Univ.eq Univ (add (inverse X) X) multiplicative_identity.
∀H11:∀X:Univ.eq Univ (add X (inverse X)) multiplicative_identity.
∀H12:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (multiply X (add Y Z)) (add (multiply X Y) (multiply X Z)).
∀H13:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (multiply (add X Y) Z) (add (multiply X Z) (multiply Y Z)).
∀H14:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (add X (multiply Y Z)) (multiply (add X Y) (add X Z)).
∀H15:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (add (multiply X Y) Z) (multiply (add X Z) (add Y Z)).
∀H16:∀X:Univ.∀Y:Univ.eq Univ (multiply X Y) (multiply Y X).
∀H17:∀X:Univ.∀Y:Univ.eq Univ (add X Y) (add Y X).eq Univ b c)
.
#Univ ##.
#X ##.
#Y ##.
#Z ##.
#a ##.
#add ##.
#additive_identity ##.
#b ##.
#c ##.
#inverse ##.
#multiplicative_identity ##.
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

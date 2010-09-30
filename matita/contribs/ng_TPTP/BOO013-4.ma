include "logic/equality.ma".

(* Inclusion of: BOO013-4.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : BOO013-4 : TPTP v3.7.0. Released v1.1.0. *)

(*  Domain   : Boolean Algebra *)

(*  Problem  : The inverse of X is unique *)

(*  Version  : [Ver94] (equality) axioms. *)

(*  English  :  *)

(*  Refs     : [Ver94] Veroff (1994), Problem Set *)

(*  Source   : [Ver94] *)

(*  Names    : TE [Ver94] *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.00 v2.2.1, 0.22 v2.2.0, 0.29 v2.1.0, 0.25 v2.0.0 *)

(*  Syntax   : Number of clauses     :   11 (   0 non-Horn;  11 unit;   3 RR) *)

(*             Number of atoms       :   11 (  11 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    7 (   4 constant; 0-2 arity) *)

(*             Number of variables   :   14 (   0 singleton) *)

(*             Maximal term depth    :    3 (   2 average) *)

(*  Comments :  *)

(* -------------------------------------------------------------------------- *)

(* ----Include boolean algebra axioms for equality formulation  *)

(* Inclusion of: Axioms/BOO004-0.ax *)

(* -------------------------------------------------------------------------- *)

(*  File     : BOO004-0 : TPTP v3.7.0. Released v1.0.0. *)

(*  Domain   : Boolean Algebra *)

(*  Axioms   : Boolean algebra (equality) axioms *)

(*  Version  : [Ver94] (equality) axioms. *)

(*  English  :  *)

(*  Refs     : [Ver94] Veroff (1994), Problem Set *)

(*  Source   : [Ver94] *)

(*  Names    :  *)

(*  Status   :  *)

(*  Syntax   : Number of clauses    :    8 (   0 non-Horn;   8 unit;   0 RR) *)

(*             Number of atoms      :    8 (   8 equality) *)

(*             Maximal clause size  :    1 (   1 average) *)

(*             Number of predicates :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors   :    5 (   2 constant; 0-2 arity) *)

(*             Number of variables  :   14 (   0 singleton) *)

(*             Maximal term depth   :    3 (   2 average) *)

(*  Comments :  *)

(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
ntheorem prove_a_inverse_is_b:
 (∀Univ:Type.∀X:Univ.∀Y:Univ.∀Z:Univ.
∀a:Univ.
∀add:∀_:Univ.∀_:Univ.Univ.
∀additive_identity:Univ.
∀b:Univ.
∀inverse:∀_:Univ.Univ.
∀multiplicative_identity:Univ.
∀multiply:∀_:Univ.∀_:Univ.Univ.
∀H0:eq Univ (multiply a b) additive_identity.
∀H1:eq Univ (add a b) multiplicative_identity.
∀H2:∀X:Univ.eq Univ (multiply X (inverse X)) additive_identity.
∀H3:∀X:Univ.eq Univ (add X (inverse X)) multiplicative_identity.
∀H4:∀X:Univ.eq Univ (multiply X multiplicative_identity) X.
∀H5:∀X:Univ.eq Univ (add X additive_identity) X.
∀H6:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (multiply X (add Y Z)) (add (multiply X Y) (multiply X Z)).
∀H7:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (add X (multiply Y Z)) (multiply (add X Y) (add X Z)).
∀H8:∀X:Univ.∀Y:Univ.eq Univ (multiply X Y) (multiply Y X).
∀H9:∀X:Univ.∀Y:Univ.eq Univ (add X Y) (add Y X).eq Univ b (inverse a))
.
#Univ ##.
#X ##.
#Y ##.
#Z ##.
#a ##.
#add ##.
#additive_identity ##.
#b ##.
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
nauto by H0,H1,H2,H3,H4,H5,H6,H7,H8,H9 ##;
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)

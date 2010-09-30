include "logic/equality.ma".

(* Inclusion of: BOO004-4.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : BOO004-4 : TPTP v3.7.0. Released v1.1.0. *)

(*  Domain   : Boolean Algebra *)

(*  Problem  : Addition is idempotent (X + X = X) *)

(*  Version  : [Ver94] (equality) axioms. *)

(*  English  :  *)

(*  Refs     : [Ver94] Veroff (1994), Problem Set *)

(*  Source   : [Ver94] *)

(*  Names    : TA [Ver94] *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.00 v2.0.0 *)

(*  Syntax   : Number of clauses     :    9 (   0 non-Horn;   9 unit;   1 RR) *)

(*             Number of atoms       :    9 (   9 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    6 (   3 constant; 0-2 arity) *)

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
ntheorem prove_a_plus_a_is_a:
 (∀Univ:Type.∀X:Univ.∀Y:Univ.∀Z:Univ.
∀a:Univ.
∀add:∀_:Univ.∀_:Univ.Univ.
∀additive_identity:Univ.
∀inverse:∀_:Univ.Univ.
∀multiplicative_identity:Univ.
∀multiply:∀_:Univ.∀_:Univ.Univ.
∀H0:∀X:Univ.eq Univ (multiply X (inverse X)) additive_identity.
∀H1:∀X:Univ.eq Univ (add X (inverse X)) multiplicative_identity.
∀H2:∀X:Univ.eq Univ (multiply X multiplicative_identity) X.
∀H3:∀X:Univ.eq Univ (add X additive_identity) X.
∀H4:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (multiply X (add Y Z)) (add (multiply X Y) (multiply X Z)).
∀H5:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (add X (multiply Y Z)) (multiply (add X Y) (add X Z)).
∀H6:∀X:Univ.∀Y:Univ.eq Univ (multiply X Y) (multiply Y X).
∀H7:∀X:Univ.∀Y:Univ.eq Univ (add X Y) (add Y X).eq Univ (add a a) a)
.
#Univ ##.
#X ##.
#Y ##.
#Z ##.
#a ##.
#add ##.
#additive_identity ##.
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
nauto by H0,H1,H2,H3,H4,H5,H6,H7 ##;
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)

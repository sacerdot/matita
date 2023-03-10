include "logic/equality.ma".

(* Inclusion of: BOO018-4.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : BOO018-4 : TPTP v3.7.0. Bugfixed v1.2.1. *)

(*  Domain   : Boolean Algebra *)

(*  Problem  : Inverse of multiplicative identity = Additive identity *)

(*  Version  : [Ver94] (equality) axioms. *)

(*  English  :  *)

(*  Refs     : [Ver94] Veroff (1994), Problem Set *)

(*  Source   : [Ver94] *)

(*  Names    : TG [Ver94] *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.00 v2.0.0 *)

(*  Syntax   : Number of clauses     :    9 (   0 non-Horn;   9 unit;   1 RR) *)

(*             Number of atoms       :    9 (   9 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    5 (   2 constant; 0-2 arity) *)

(*             Number of variables   :   14 (   0 singleton) *)

(*             Maximal term depth    :    3 (   2 average) *)

(*  Comments :  *)

(*  Bugfixes : v1.2.1 - Clause prove_inverse_of_1_is_0 fixed. *)

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
ntheorem prove_inverse_of_1_is_0:
 (???Univ:Type.???X:Univ.???Y:Univ.???Z:Univ.
???add:???_:Univ.???_:Univ.Univ.
???additive_identity:Univ.
???inverse:???_:Univ.Univ.
???multiplicative_identity:Univ.
???multiply:???_:Univ.???_:Univ.Univ.
???H0:???X:Univ.eq Univ (multiply X (inverse X)) additive_identity.
???H1:???X:Univ.eq Univ (add X (inverse X)) multiplicative_identity.
???H2:???X:Univ.eq Univ (multiply X multiplicative_identity) X.
???H3:???X:Univ.eq Univ (add X additive_identity) X.
???H4:???X:Univ.???Y:Univ.???Z:Univ.eq Univ (multiply X (add Y Z)) (add (multiply X Y) (multiply X Z)).
???H5:???X:Univ.???Y:Univ.???Z:Univ.eq Univ (add X (multiply Y Z)) (multiply (add X Y) (add X Z)).
???H6:???X:Univ.???Y:Univ.eq Univ (multiply X Y) (multiply Y X).
???H7:???X:Univ.???Y:Univ.eq Univ (add X Y) (add Y X).eq Univ (inverse multiplicative_identity) additive_identity)
.
#Univ ##.
#X ##.
#Y ##.
#Z ##.
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

include "logic/equality.ma".

(* Inclusion of: BOO015-2.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : BOO015-2 : TPTP v3.7.0. Bugfixed v1.0.1. *)

(*  Domain   : Boolean Algebra *)

(*  Problem  : DeMorgan for inverse and sum (X^-1 + Y^-1) = (X * Y)^-1 *)

(*  Version  : [ANL] (equality) axioms. *)

(*  English  :  *)

(*  Refs     :  *)

(*  Source   : [ANL] *)

(*  Names    : prob10.ver2.in [ANL] *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.00 v2.2.1, 0.22 v2.2.0, 0.29 v2.1.0, 0.62 v2.0.0 *)

(*  Syntax   : Number of clauses     :   17 (   0 non-Horn;  17 unit;   3 RR) *)

(*             Number of atoms       :   17 (  17 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    9 (   6 constant; 0-2 arity) *)

(*             Number of variables   :   24 (   0 singleton) *)

(*             Maximal term depth    :    3 (   2 average) *)

(*  Comments :  *)

(*  Bugfixes : v1.0.1 - Clause a_inverse_plus_b_inverse_is_d fixed. *)

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
ntheorem prove_c_inverse_is_d:
 (???Univ:Type.???X:Univ.???Y:Univ.???Z:Univ.
???a:Univ.
???add:???_:Univ.???_:Univ.Univ.
???additive_identity:Univ.
???b:Univ.
???c:Univ.
???d:Univ.
???inverse:???_:Univ.Univ.
???multiplicative_identity:Univ.
???multiply:???_:Univ.???_:Univ.Univ.
???H0:eq Univ (add (inverse a) (inverse b)) d.
???H1:eq Univ (multiply a b) c.
???H2:???X:Univ.eq Univ (add additive_identity X) X.
???H3:???X:Univ.eq Univ (add X additive_identity) X.
???H4:???X:Univ.eq Univ (multiply multiplicative_identity X) X.
???H5:???X:Univ.eq Univ (multiply X multiplicative_identity) X.
???H6:???X:Univ.eq Univ (multiply (inverse X) X) additive_identity.
???H7:???X:Univ.eq Univ (multiply X (inverse X)) additive_identity.
???H8:???X:Univ.eq Univ (add (inverse X) X) multiplicative_identity.
???H9:???X:Univ.eq Univ (add X (inverse X)) multiplicative_identity.
???H10:???X:Univ.???Y:Univ.???Z:Univ.eq Univ (multiply X (add Y Z)) (add (multiply X Y) (multiply X Z)).
???H11:???X:Univ.???Y:Univ.???Z:Univ.eq Univ (multiply (add X Y) Z) (add (multiply X Z) (multiply Y Z)).
???H12:???X:Univ.???Y:Univ.???Z:Univ.eq Univ (add X (multiply Y Z)) (multiply (add X Y) (add X Z)).
???H13:???X:Univ.???Y:Univ.???Z:Univ.eq Univ (add (multiply X Y) Z) (multiply (add X Z) (add Y Z)).
???H14:???X:Univ.???Y:Univ.eq Univ (multiply X Y) (multiply Y X).
???H15:???X:Univ.???Y:Univ.eq Univ (add X Y) (add Y X).eq Univ (inverse c) d)
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
#d ##.
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
nauto by H0,H1,H2,H3,H4,H5,H6,H7,H8,H9,H10,H11,H12,H13,H14,H15 ##;
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)

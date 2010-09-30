include "logic/equality.ma".

(* Inclusion of: BOO029-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : BOO029-1 : TPTP v3.7.0. Released v2.2.0. *)

(*  Domain   : Boolean Algebra *)

(*  Problem  : Self-dual 2-basis from majority reduction, part 3. *)

(*  Version  : [MP96] (equality) axioms : Especial. *)

(*  English  : This is part of a proof that there exists an independent *)

(*             self-dual-2-basis for Boolean algebra by majority reduction. *)

(*  Refs     : [McC98] McCune (1998), Email to G. Sutcliffe *)

(*           : [MP96]  McCune & Padmanabhan (1996), Automated Deduction in Eq *)

(*  Source   : [McC98] *)

(*  Names    : DUAL-BA-5-c [MP96] *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.00 v2.2.1 *)

(*  Syntax   : Number of clauses     :   11 (   0 non-Horn;  11 unit;   1 RR) *)

(*             Number of atoms       :   11 (  11 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    5 (   2 constant; 0-2 arity) *)

(*             Number of variables   :   26 (   8 singleton) *)

(*             Maximal term depth    :    4 (   3 average) *)

(*  Comments : *)

(* -------------------------------------------------------------------------- *)

(* ----Properties L1, L3, and B1 of Boolean Algebra: *)

(* ----The corresponding dual properties L2, L4, and B2. *)

(* ----Associativity and Commutativity of both operations: *)

(* ----Denial of conclusion: *)
ntheorem prove_equal_inverse:
 (∀Univ:Type.∀X:Univ.∀Y:Univ.∀Z:Univ.
∀a:Univ.
∀add:∀_:Univ.∀_:Univ.Univ.
∀b:Univ.
∀inverse:∀_:Univ.Univ.
∀multiply:∀_:Univ.∀_:Univ.Univ.
∀H0:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (multiply (multiply X Y) Z) (multiply X (multiply Y Z)).
∀H1:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (add (add X Y) Z) (add X (add Y Z)).
∀H2:∀X:Univ.∀Y:Univ.eq Univ (multiply X Y) (multiply Y X).
∀H3:∀X:Univ.∀Y:Univ.eq Univ (add X Y) (add Y X).
∀H4:∀X:Univ.∀Y:Univ.eq Univ (add (multiply X Y) (multiply X (inverse Y))) X.
∀H5:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (multiply (multiply (add X Y) (add Y Z)) Y) Y.
∀H6:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (multiply X (add Y (add X Z))) X.
∀H7:∀X:Univ.∀Y:Univ.eq Univ (multiply (add X Y) (add X (inverse Y))) X.
∀H8:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (add (add (multiply X Y) (multiply Y Z)) Y) Y.
∀H9:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (add X (multiply Y (multiply X Z))) X.eq Univ (add b (inverse b)) (add a (inverse a)))
.
#Univ ##.
#X ##.
#Y ##.
#Z ##.
#a ##.
#add ##.
#b ##.
#inverse ##.
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

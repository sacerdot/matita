include "logic/equality.ma".

(* Inclusion of: BOO032-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : BOO032-1 : TPTP v3.7.0. Released v2.2.0. *)

(*  Domain   : Boolean Algebra *)

(*  Problem  : Independence of a system of Boolean algebra *)

(*  Version  : [MP96] (equality) axioms : Especial. *)

(*  English  : This is part of a proof that a self-dual 3-basis for Boolean  *)

(*             algebra is independent. *)

(*  Refs     : [McC98] McCune (1998), Email to G. Sutcliffe *)

(*           : [MP96]  McCune & Padmanabhan (1996), Automated Deduction in Eq *)

(*  Source   : [McC98] *)

(*  Names    : DUAL-BA-9 [MP96] *)

(*  Status   : Satisfiable *)

(*  Rating   : 0.33 v3.2.0, 0.67 v3.1.0, 0.33 v2.5.0, 0.67 v2.4.0, 0.67 v2.3.0, 1.00 v2.2.1 *)

(*  Syntax   : Number of clauses     :   13 (   0 non-Horn;  13 unit;   1 RR) *)

(*             Number of atoms       :   13 (  13 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    4 (   1 constant; 0-2 arity) *)

(*             Number of variables   :   28 (  10 singleton) *)

(*             Maximal term depth    :    4 (   2 average) *)

(*  Comments : The smallest model has 5 elements. *)

(* -------------------------------------------------------------------------- *)

(* ----3 properties of Boolean algebra and the corresponding duals. *)

(* ----Majority polynomials: *)

(* ----Duals of majority polynomials: *)

(* ----A propery of Boolean Algebra fails to hold. *)
ntheorem prove_inverse_involution:
 (∀Univ:Type.∀X:Univ.∀Y:Univ.∀Z:Univ.
∀a:Univ.
∀add:∀_:Univ.∀_:Univ.Univ.
∀inverse:∀_:Univ.Univ.
∀multiply:∀_:Univ.∀_:Univ.Univ.
∀H0:∀X:Univ.∀Y:Univ.eq Univ (multiply (add (multiply X Y) Y) (add X Y)) Y.
∀H1:∀X:Univ.∀Y:Univ.eq Univ (multiply (add (multiply X X) Y) (add X X)) X.
∀H2:∀X:Univ.∀Y:Univ.eq Univ (multiply (add (multiply X Y) X) (add X Y)) X.
∀H3:∀X:Univ.∀Y:Univ.eq Univ (add (multiply (add X Y) Y) (multiply X Y)) Y.
∀H4:∀X:Univ.∀Y:Univ.eq Univ (add (multiply (add X X) Y) (multiply X X)) X.
∀H5:∀X:Univ.∀Y:Univ.eq Univ (add (multiply (add X Y) X) (multiply X Y)) X.
∀H6:∀X:Univ.∀Y:Univ.eq Univ (add (multiply X (inverse X)) Y) Y.
∀H7:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (multiply (multiply (add X Y) (add Y Z)) Y) Y.
∀H8:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (multiply X (add Y (add X Z))) X.
∀H9:∀X:Univ.∀Y:Univ.eq Univ (multiply (add X (inverse X)) Y) Y.
∀H10:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (add (add (multiply X Y) (multiply Y Z)) Y) Y.
∀H11:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (add X (multiply Y (multiply X Z))) X.eq Univ (inverse (inverse a)) a)
.
#Univ ##.
#X ##.
#Y ##.
#Z ##.
#a ##.
#add ##.
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
#H10 ##.
#H11 ##.
nauto by H0,H1,H2,H3,H4,H5,H6,H7,H8,H9,H10,H11 ##;
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)

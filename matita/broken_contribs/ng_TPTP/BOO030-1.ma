include "logic/equality.ma".

(* Inclusion of: BOO030-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : BOO030-1 : TPTP v3.7.0. Released v2.2.0. *)

(*  Domain   : Boolean Algebra *)

(*  Problem  : Independence of a BA 2-basis by majority reduction. *)

(*  Version  : [MP96] (equality) axioms : Especial. *)

(*  English  : This shows that the self-dual 2-basis for Boolean algebra *)

(*             (majority reduction) of problem DUAL-BA-5 is independent, *)

(*             in particular, that half of the 2-basis is not a basis. *)

(*  Refs     : [McC98] McCune (1998), Email to G. Sutcliffe *)

(*           : [MP96]  McCune & Padmanabhan (1996), Automated Deduction in Eq *)

(*  Source   : [McC98] *)

(*  Names    : DUAL-BA-6 [MP96] *)

(*  Status   : Satisfiable *)

(*  Rating   : 0.33 v3.2.0, 0.67 v3.1.0, 0.33 v2.4.0, 0.67 v2.3.0, 1.00 v2.2.1 *)

(*  Syntax   : Number of clauses     :    7 (   0 non-Horn;   7 unit;   1 RR) *)

(*             Number of atoms       :    7 (   7 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    4 (   1 constant; 0-2 arity) *)

(*             Number of variables   :   14 (   5 singleton) *)

(*             Maximal term depth    :    4 (   2 average) *)

(*  Comments : There is a 2-element model. *)

(* -------------------------------------------------------------------------- *)

(* ----Properties L1, L3, and B1 of Boolean Algebra: *)

(* ----Majority reduction properties: *)

(* ----Denial of a property of Boolean Algebra. *)
ntheorem prove_inverse_involution:
 (∀Univ:Type.∀X:Univ.∀Y:Univ.∀Z:Univ.
∀a:Univ.
∀add:∀_:Univ.∀_:Univ.Univ.
∀inverse:∀_:Univ.Univ.
∀multiply:∀_:Univ.∀_:Univ.Univ.
∀H0:∀X:Univ.∀Y:Univ.eq Univ (multiply (add (multiply X Y) Y) (add X Y)) Y.
∀H1:∀X:Univ.∀Y:Univ.eq Univ (multiply (add (multiply X X) Y) (add X X)) X.
∀H2:∀X:Univ.∀Y:Univ.eq Univ (multiply (add (multiply X Y) X) (add X Y)) X.
∀H3:∀X:Univ.∀Y:Univ.eq Univ (multiply (add X Y) (add X (inverse Y))) X.
∀H4:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (add (add (multiply X Y) (multiply Y Z)) Y) Y.
∀H5:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (add X (multiply Y (multiply X Z))) X.eq Univ (inverse (inverse a)) a)
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
nauto by H0,H1,H2,H3,H4,H5 ##;
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)

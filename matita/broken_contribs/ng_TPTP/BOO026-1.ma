include "logic/equality.ma".

(* Inclusion of: BOO026-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : BOO026-1 : TPTP v3.7.0. Released v2.2.0. *)

(*  Domain   : Boolean Algebra *)

(*  Problem  : Absorption from self-dual independent 2-basis *)

(*  Version  : [MP96] (eqiality) axioms : Especial. *)

(*  English  : This is part of a proof that there exists an independent self-dual *)

(*             2-basis for Boolean Algebra.  You may note that the basis *)

(*             below has more than 2 equations; but don't worry, it can be *)

(*             reduced to 2 (large) equations by Pixley reduction. *)

(*  Refs     : [Wos98] Wos (1998), Automating the Search for Elegant Proofs *)

(*           : [McC98] McCune (1998), Email to G. Sutcliffe *)

(*           : [MP96]  McCune & Padmanabhan (1996), Automated Deduction in Eq *)

(*  Source   : [McC98] *)

(*  Names    : DUAL-BA-3 [MP96] *)

(*           : DUAL-BA-3 [Wos98] *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.11 v3.4.0, 0.12 v3.3.0, 0.07 v3.1.0, 0.11 v2.7.0, 0.00 v2.2.1 *)

(*  Syntax   : Number of clauses     :   11 (   0 non-Horn;  11 unit;   1 RR) *)

(*             Number of atoms       :   11 (  11 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    7 (   4 constant; 0-2 arity) *)

(*             Number of variables   :   20 (   0 singleton) *)

(*             Maximal term depth    :    5 (   3 average) *)

(*  Comments : The original proof has 816 steps.  Wos later found a 99-step *)

(*             proof. *)

(* -------------------------------------------------------------------------- *)

(* ----Two Boolean algebra properties and their duals: *)

(* ----Expanded Pixley properties and their duals: *)

(* ----Denial of the conclusion: *)
ntheorem prove_multiply_add:
 (∀Univ:Type.∀X:Univ.∀Y:Univ.∀Z:Univ.
∀a:Univ.
∀add:∀_:Univ.∀_:Univ.Univ.
∀b:Univ.
∀inverse:∀_:Univ.Univ.
∀multiply:∀_:Univ.∀_:Univ.Univ.
∀n0:Univ.
∀n1:Univ.
∀H0:∀X:Univ.∀Y:Univ.eq Univ (multiply (add X (inverse Y)) (multiply (add X X) (add (inverse Y) X))) X.
∀H1:∀X:Univ.∀Y:Univ.eq Univ (multiply (add X (inverse Y)) (multiply (add X Y) (add (inverse Y) Y))) X.
∀H2:∀X:Univ.∀Y:Univ.eq Univ (multiply (add X (inverse X)) (multiply (add X Y) (add (inverse X) Y))) Y.
∀H3:∀X:Univ.∀Y:Univ.eq Univ (add (multiply X (inverse Y)) (add (multiply X X) (multiply (inverse Y) X))) X.
∀H4:∀X:Univ.∀Y:Univ.eq Univ (add (multiply X (inverse Y)) (add (multiply X Y) (multiply (inverse Y) Y))) X.
∀H5:∀X:Univ.∀Y:Univ.eq Univ (add (multiply X (inverse X)) (add (multiply X Y) (multiply (inverse X) Y))) Y.
∀H6:∀X:Univ.eq Univ (multiply X (inverse X)) n0.
∀H7:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (add X (multiply Y Z)) (multiply (add Y X) (add Z X)).
∀H8:∀X:Univ.eq Univ (add X (inverse X)) n1.
∀H9:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (multiply X (add Y Z)) (add (multiply Y X) (multiply Z X)).eq Univ (multiply (add a b) b) b)
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
#n0 ##.
#n1 ##.
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

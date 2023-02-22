include "logic/equality.ma".

(* Inclusion of: BOO024-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : BOO024-1 : TPTP v3.7.0. Released v2.2.0. *)

(*  Domain   : Boolean Algebra *)

(*  Problem  : Half of Padmanabhan's 6-basis with Pixley, part 2. *)

(*  Version  : [MP96] (equality) axioms : Especial. *)

(*  English  : Part 2 (of 3) of the proof that half of Padmanaban's self-dual *)

(*             independent 6-basis for Boolean Algebra, together with a Pixley *)

(*             polynomial, is a basis for Boolean algebra. *)

(*  Refs     : [McC98] McCune (1998), Email to G. Sutcliffe *)

(*           : [MP96]  McCune & Padmanabhan (1996), Automated Deduction in Eq *)

(*  Source   : [McC98] *)

(*  Names    : DUAL-BA-2-b [MP96] *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.11 v3.4.0, 0.12 v3.3.0, 0.00 v2.2.1 *)

(*  Syntax   : Number of clauses     :    8 (   0 non-Horn;   8 unit;   1 RR) *)

(*             Number of atoms       :    8 (   8 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    7 (   3 constant; 0-3 arity) *)

(*             Number of variables   :   15 (   2 singleton) *)

(*             Maximal term depth    :    5 (   2 average) *)

(*  Comments : *)

(* -------------------------------------------------------------------------- *)

(* ----Half of Padmanabhan's self-dual independent 6-basis for Boolean Algebra: *)

(* ----pixley(X,Y,Z) is a Pixley polynomial: *)

(* ----Denial of conclusion: *)
ntheorem prove_add_multiply:
 (∀Univ:Type.∀X:Univ.∀Y:Univ.∀Z:Univ.
∀a:Univ.
∀add:∀_:Univ.∀_:Univ.Univ.
∀b:Univ.
∀inverse:∀_:Univ.Univ.
∀multiply:∀_:Univ.∀_:Univ.Univ.
∀n1:Univ.
∀pixley:∀_:Univ.∀_:Univ.∀_:Univ.Univ.
∀H0:∀X:Univ.∀Y:Univ.eq Univ (pixley X Y X) X.
∀H1:∀X:Univ.∀Y:Univ.eq Univ (pixley X Y Y) X.
∀H2:∀X:Univ.∀Y:Univ.eq Univ (pixley X X Y) Y.
∀H3:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (pixley X Y Z) (add (multiply X (inverse Y)) (add (multiply X Z) (multiply (inverse Y) Z))).
∀H4:∀X:Univ.eq Univ (add X (inverse X)) n1.
∀H5:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (multiply X (add Y Z)) (add (multiply Y X) (multiply Z X)).
∀H6:∀X:Univ.∀Y:Univ.eq Univ (multiply (add X Y) Y) Y.eq Univ (add (multiply a b) b) b)
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
#n1 ##.
#pixley ##.
#H0 ##.
#H1 ##.
#H2 ##.
#H3 ##.
#H4 ##.
#H5 ##.
#H6 ##.
nauto by H0,H1,H2,H3,H4,H5,H6 ##;
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)

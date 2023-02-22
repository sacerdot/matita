include "logic/equality.ma".

(* Inclusion of: BOO027-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : BOO027-1 : TPTP v3.7.0. Released v2.2.0. *)

(*  Domain   : Boolean Algebra *)

(*  Problem  : Independence of self-dual 2-basis. *)

(*  Version  : [MP96] (eqiality) axioms : Especial. *)

(*  English  : Show that half of the self-dual 2-basis in DUAL-BA-3 is not *)

(*             a basis for Boolean Algebra. *)

(*  Refs     : [McC98] McCune (1998), Email to G. Sutcliffe *)

(*           : [MP96]  McCune & Padmanabhan (1996), Automated Deduction in Eq *)

(*  Source   : [McC98] *)

(*  Names    : DUAL-BA-4 [MP96] *)

(*  Status   : Satisfiable *)

(*  Rating   : 0.00 v3.2.0, 0.33 v3.1.0, 0.00 v2.2.1 *)

(*  Syntax   : Number of clauses     :    6 (   0 non-Horn;   6 unit;   1 RR) *)

(*             Number of atoms       :    6 (   6 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    5 (   2 constant; 0-2 arity) *)

(*             Number of variables   :   10 (   0 singleton) *)

(*             Maximal term depth    :    5 (   3 average) *)

(*  Comments : There is a 2-element model. *)

(* -------------------------------------------------------------------------- *)

(* ----Two properties of Boolean algebra: *)

(* ----Pixley properties: *)

(* ----Denial of a property of Boolean Algebra: *)
ntheorem prove_idempotence:
 (∀Univ:Type.∀X:Univ.∀Y:Univ.∀Z:Univ.
∀a:Univ.
∀add:∀_:Univ.∀_:Univ.Univ.
∀inverse:∀_:Univ.Univ.
∀multiply:∀_:Univ.∀_:Univ.Univ.
∀one:Univ.
∀H0:∀X:Univ.∀Y:Univ.eq Univ (add (multiply X (inverse Y)) (add (multiply X X) (multiply (inverse Y) X))) X.
∀H1:∀X:Univ.∀Y:Univ.eq Univ (add (multiply X (inverse Y)) (add (multiply X Y) (multiply (inverse Y) Y))) X.
∀H2:∀X:Univ.∀Y:Univ.eq Univ (add (multiply X (inverse X)) (add (multiply X Y) (multiply (inverse X) Y))) Y.
∀H3:∀X:Univ.eq Univ (add X (inverse X)) one.
∀H4:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (multiply X (add Y Z)) (add (multiply Y X) (multiply Z X)).eq Univ (add a a) a)
.
#Univ ##.
#X ##.
#Y ##.
#Z ##.
#a ##.
#add ##.
#inverse ##.
#multiply ##.
#one ##.
#H0 ##.
#H1 ##.
#H2 ##.
#H3 ##.
#H4 ##.
nauto by H0,H1,H2,H3,H4 ##;
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)

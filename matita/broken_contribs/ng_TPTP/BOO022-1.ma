include "logic/equality.ma".

(* Inclusion of: BOO022-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : BOO022-1 : TPTP v3.7.0. Released v2.2.0. *)

(*  Domain   : Boolean Algebra *)

(*  Problem  : A Basis for Boolean Algebra *)

(*  Version  : [MP96] (equality) axioms. *)

(*  English  : This ntheorem starts with a (self-dual independent) 6-basis *)

(*             for Boolean algebra and derives associativity of product. *)

(*  Refs     : [McC98] McCune (1998), Email to G. Sutcliffe *)

(*           : [MP96]  McCune & Padmanabhan (1996), Automated Deduction in Eq *)

(*  Source   : [McC98] *)

(*  Names    : DUAL-BA-1 [MP96] *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.11 v3.4.0, 0.12 v3.3.0, 0.14 v3.2.0, 0.07 v3.1.0, 0.22 v2.7.0, 0.00 v2.2.1 *)

(*  Syntax   : Number of clauses     :    7 (   0 non-Horn;   7 unit;   1 RR) *)

(*             Number of atoms       :    7 (   7 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    8 (   5 constant; 0-2 arity) *)

(*             Number of variables   :   12 (   2 singleton) *)

(*             Maximal term depth    :    3 (   2 average) *)

(*  Comments : The other part of this problem is to prove commutativity. *)

(* -------------------------------------------------------------------------- *)

(* ----Boolean Algebra: *)

(* ----Denial of conclusion: *)
ntheorem prove_associativity_of_multiply:
 (∀Univ:Type.∀X:Univ.∀Y:Univ.∀Z:Univ.
∀a:Univ.
∀add:∀_:Univ.∀_:Univ.Univ.
∀b:Univ.
∀c:Univ.
∀inverse:∀_:Univ.Univ.
∀multiply:∀_:Univ.∀_:Univ.Univ.
∀n0:Univ.
∀n1:Univ.
∀H0:∀X:Univ.eq Univ (multiply X (inverse X)) n0.
∀H1:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (add X (multiply Y Z)) (multiply (add Y X) (add Z X)).
∀H2:∀X:Univ.∀Y:Univ.eq Univ (add (multiply X Y) Y) Y.
∀H3:∀X:Univ.eq Univ (add X (inverse X)) n1.
∀H4:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (multiply X (add Y Z)) (add (multiply Y X) (multiply Z X)).
∀H5:∀X:Univ.∀Y:Univ.eq Univ (multiply (add X Y) Y) Y.eq Univ (multiply (multiply a b) c) (multiply a (multiply b c)))
.
#Univ ##.
#X ##.
#Y ##.
#Z ##.
#a ##.
#add ##.
#b ##.
#c ##.
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
nauto by H0,H1,H2,H3,H4,H5 ##;
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)

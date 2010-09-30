include "logic/equality.ma".

(* Inclusion of: BOO031-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : BOO031-1 : TPTP v3.7.0. Released v2.2.0. *)

(*  Domain   : Boolean Algebra *)

(*  Problem  : Dual BA 3-basis, proof of distributivity. *)

(*  Version  : [MP96] (equality) axioms : Especial. *)

(*  English  : This is part of a proof of the existence of a self-dual *)

(*             3-basis for Boolean algebra by majority reduction. *)

(*  Refs     : [McC98] McCune (1998), Email to G. Sutcliffe *)

(*           : [MP96]  McCune & Padmanabhan (1996), Automated Deduction in Eq *)

(*  Source   : [McC98] *)

(*  Names    : DUAL-BA-8-a [MP96] *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.22 v3.4.0, 0.25 v3.3.0, 0.29 v3.2.0, 0.21 v3.1.0, 0.22 v2.7.0, 0.09 v2.6.0, 0.17 v2.5.0, 0.00 v2.4.0, 0.00 v2.2.1 *)

(*  Syntax   : Number of clauses     :   12 (   0 non-Horn;  12 unit;   1 RR) *)

(*             Number of atoms       :   12 (  12 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    8 (   5 constant; 0-2 arity) *)

(*             Number of variables   :   27 (   8 singleton) *)

(*             Maximal term depth    :    4 (   3 average) *)

(*  Comments : *)

(* -------------------------------------------------------------------------- *)

(* ----Self-dual distributivity: *)

(* ----3 properties of Boolean algebra and the corresponding duals. *)

(* ----Existence of 0 and 1. *)

(* ----Associativity of the 2 operations. *)

(* ----Denial of conclusion: *)
ntheorem prove_multiply_add_property:
 (∀Univ:Type.∀X:Univ.∀Y:Univ.∀Z:Univ.
∀a:Univ.
∀add:∀_:Univ.∀_:Univ.Univ.
∀b:Univ.
∀c:Univ.
∀inverse:∀_:Univ.Univ.
∀multiply:∀_:Univ.∀_:Univ.Univ.
∀n0:Univ.
∀n1:Univ.
∀H0:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (multiply (multiply X Y) Z) (multiply X (multiply Y Z)).
∀H1:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (add (add X Y) Z) (add X (add Y Z)).
∀H2:∀X:Univ.eq Univ (multiply X (inverse X)) n0.
∀H3:∀X:Univ.eq Univ (add X (inverse X)) n1.
∀H4:∀X:Univ.∀Y:Univ.eq Univ (add (multiply X (inverse X)) Y) Y.
∀H5:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (multiply (multiply (add X Y) (add Y Z)) Y) Y.
∀H6:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (multiply X (add Y (add X Z))) X.
∀H7:∀X:Univ.∀Y:Univ.eq Univ (multiply (add X (inverse X)) Y) Y.
∀H8:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (add (add (multiply X Y) (multiply Y Z)) Y) Y.
∀H9:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (add X (multiply Y (multiply X Z))) X.
∀H10:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (add (multiply X Y) (add (multiply Y Z) (multiply Z X))) (multiply (add X Y) (multiply (add Y Z) (add Z X))).eq Univ (multiply a (add b c)) (add (multiply b a) (multiply c a)))
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
#H6 ##.
#H7 ##.
#H8 ##.
#H9 ##.
#H10 ##.
nauto by H0,H1,H2,H3,H4,H5,H6,H7,H8,H9,H10 ##;
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)

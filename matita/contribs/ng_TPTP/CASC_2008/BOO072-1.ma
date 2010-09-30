include "logic/equality.ma".

(* Inclusion of: BOO072-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : BOO072-1 : TPTP v3.7.0. Released v2.6.0. *)

(*  Domain   : Boolean Algebra *)

(*  Problem  : DN-1 is a single axiom for Boolean algebra, part 1 *)

(*  Version  : [EF+02] axioms. *)

(*  English  :  *)

(*  Refs     : [EF+02] Ernst et al. (2002), More First-order Test Problems in *)

(*           : [MV+02] McCune et al. (2002), Short Single Axioms for Boolean *)

(*  Source   : [TPTP] *)

(*  Names    :  *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.22 v3.4.0, 0.25 v3.3.0, 0.07 v3.1.0, 0.00 v2.7.0, 0.09 v2.6.0 *)

(*  Syntax   : Number of clauses     :    2 (   0 non-Horn;   2 unit;   1 RR) *)

(*             Number of atoms       :    2 (   2 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    4 (   2 constant; 0-2 arity) *)

(*             Number of variables   :    4 (   2 singleton) *)

(*             Maximal term depth    :    9 (   4 average) *)

(*  Comments : A UEQ part of BOO038-1 *)

(* -------------------------------------------------------------------------- *)
ntheorem huntinton_1:
 (∀Univ:Type.∀A:Univ.∀B:Univ.∀C:Univ.∀D:Univ.
∀a:Univ.
∀add:∀_:Univ.∀_:Univ.Univ.
∀b:Univ.
∀inverse:∀_:Univ.Univ.
∀H0:∀A:Univ.∀B:Univ.∀C:Univ.∀D:Univ.eq Univ (inverse (add (inverse (add (inverse (add A B)) C)) (inverse (add A (inverse (add (inverse C) (inverse (add C D)))))))) C.eq Univ (add b a) (add a b))
.
#Univ ##.
#A ##.
#B ##.
#C ##.
#D ##.
#a ##.
#add ##.
#b ##.
#inverse ##.
#H0 ##.
nauto by H0 ##;
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)

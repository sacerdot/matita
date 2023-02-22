include "logic/equality.ma".

(* Inclusion of: BOO087-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : BOO087-1 : TPTP v3.7.0. Released v2.6.0. *)

(*  Domain   : Boolean Algebra *)

(*  Problem  : Axiom C6 for Boolean algebra in the Sheffer stroke, part 1 *)

(*  Version  : [EF+02] axioms. *)

(*  English  :  *)

(*  Refs     : [EF+02] Ernst et al. (2002), More First-order Test Problems in *)

(*           : [MV+02] McCune et al. (2002), Short Single Axioms for Boolean *)

(*  Source   : [TPTP] *)

(*  Names    :  *)

(*  Status   : Unknown *)

(*  Rating   : 1.00 v2.6.0 *)

(*  Syntax   : Number of clauses     :    2 (   0 non-Horn;   2 unit;   1 RR) *)

(*             Number of atoms       :    2 (   2 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    3 (   2 constant; 0-2 arity) *)

(*             Number of variables   :    3 (   0 singleton) *)

(*             Maximal term depth    :    5 (   2 average) *)

(*  Comments : A UEQ part of BOO045-1 *)

(* -------------------------------------------------------------------------- *)
ntheorem prove_meredith_2_basis_1:
 (∀Univ:Type.∀A:Univ.∀B:Univ.∀C:Univ.
∀a:Univ.
∀b:Univ.
∀nand:∀_:Univ.∀_:Univ.Univ.
∀H0:∀A:Univ.∀B:Univ.∀C:Univ.eq Univ (nand (nand A (nand A (nand B C))) (nand C (nand A B))) C.eq Univ (nand (nand a a) (nand b a)) a)
.
#Univ ##.
#A ##.
#B ##.
#C ##.
#a ##.
#b ##.
#nand ##.
#H0 ##.
nauto by H0 ##;
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)

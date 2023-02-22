include "logic/equality.ma".

(* Inclusion of: COL029-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : COL029-1 : TPTP v3.7.0. Released v1.0.0. *)

(*  Domain   : Combinatory Logic *)

(*  Problem  : Strong fixed point for U *)

(*  Version  : [WM88] (equality) axioms. *)

(*  English  : The strong fixed point property holds for the set  *)

(*             P consisting of the combinator U, where (Ux)y = y((xx)y). *)

(*  Refs     : [Smu85] Smullyan (1978), To Mock a Mocking Bird and Other Logi *)

(*           : [MW87]  McCune & Wos (1987), A Case Study in Automated Theorem *)

(*           : [WM88]  Wos & McCune (1988), Challenge Problems Focusing on Eq *)

(*           : [MW88]  McCune & Wos (1988), Some Fixed Point Problems in Comb *)

(*           : [Wos93] Wos (1993), The Kernel Strategy and Its Use for the St *)

(*  Source   : [MW88] *)

(*  Names    : - [MW88] *)

(*           : Question 1 [Wos93] *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.00 v2.0.0 *)

(*  Syntax   : Number of clauses     :    2 (   0 non-Horn;   2 unit;   1 RR) *)

(*             Number of atoms       :    2 (   2 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    3 (   1 constant; 0-2 arity) *)

(*             Number of variables   :    3 (   0 singleton) *)

(*             Maximal term depth    :    4 (   4 average) *)

(*  Comments :  *)

(* -------------------------------------------------------------------------- *)
ntheorem prove_fixed_point:
 (∀Univ:Type.∀X:Univ.∀Y:Univ.
∀apply:∀_:Univ.∀_:Univ.Univ.
∀f:∀_:Univ.Univ.
∀u:Univ.
∀H0:∀X:Univ.∀Y:Univ.eq Univ (apply (apply u X) Y) (apply Y (apply (apply X X) Y)).∃Y:Univ.eq Univ (apply Y (f Y)) (apply (f Y) (apply Y (f Y))))
.
#Univ ##.
#X ##.
#Y ##.
#apply ##.
#f ##.
#u ##.
#H0 ##.
napply (ex_intro ? ? ? ?) ##[
##2:
nauto by H0 ##;
##| ##skip ##]
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)

include "logic/equality.ma".

(* Inclusion of: COL044-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : COL044-1 : TPTP v3.7.0. Released v1.0.0. *)

(*  Domain   : Combinatory Logic *)

(*  Problem  : Strong fixed point for B and N *)

(*  Version  : [WM88] (equality) axioms. *)

(*  English  : The strong fixed point property holds for the set  *)

(*             P consisting of the combinators B and N, where ((Bx)y)z  *)

(*             = x(yz), ((Nx)y)z = ((xz)y)z. *)

(*  Refs     : [Smu85] Smullyan (1978), To Mock a Mocking Bird and Other Logi *)

(*           : [MW87]  McCune & Wos (1987), A Case Study in Automated Theorem *)

(*           : [WM88]  Wos & McCune (1988), Challenge Problems Focusing on Eq *)

(*           : [MW88]  McCune & Wos (1988), Some Fixed Point Problems in Comb *)

(*           : [LW92]  Lusk & Wos (1992), Benchmark Problems in Which Equalit *)

(*           : [Wos93] Wos (1993), The Kernel Strategy and Its Use for the St *)

(*  Source   : [MW88] *)

(*  Names    : - [MW88] *)

(*           : CL3 [LW92] *)

(*           : Question 5 [Wos93] *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.22 v3.4.0, 0.25 v3.3.0, 0.29 v3.2.0, 0.21 v3.1.0, 0.22 v2.7.0, 0.18 v2.6.0, 0.33 v2.5.0, 0.00 v2.2.1, 0.11 v2.2.0, 0.00 v2.1.0, 0.25 v2.0.0 *)

(*  Syntax   : Number of clauses     :    3 (   0 non-Horn;   3 unit;   1 RR) *)

(*             Number of atoms       :    3 (   3 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    4 (   2 constant; 0-2 arity) *)

(*             Number of variables   :    7 (   0 singleton) *)

(*             Maximal term depth    :    4 (   4 average) *)

(*  Comments :  *)

(* -------------------------------------------------------------------------- *)
ntheorem prove_fixed_point:
 (∀Univ:Type.∀X:Univ.∀Y:Univ.∀Z:Univ.
∀apply:∀_:Univ.∀_:Univ.Univ.
∀b:Univ.
∀f:∀_:Univ.Univ.
∀n:Univ.
∀H0:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (apply (apply (apply n X) Y) Z) (apply (apply (apply X Z) Y) Z).
∀H1:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (apply (apply (apply b X) Y) Z) (apply X (apply Y Z)).∃Y:Univ.eq Univ (apply Y (f Y)) (apply (f Y) (apply Y (f Y))))
.
#Univ ##.
#X ##.
#Y ##.
#Z ##.
#apply ##.
#b ##.
#f ##.
#n ##.
#H0 ##.
#H1 ##.
napply (ex_intro ? ? ? ?) ##[
##2:
nauto by H0,H1 ##;
##| ##skip ##]
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)

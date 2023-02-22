include "logic/equality.ma".

(* Inclusion of: COL046-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : COL046-1 : TPTP v3.7.0. Released v1.0.0. *)

(*  Domain   : Combinatory Logic *)

(*  Problem  : Strong fixed point for B, M and S *)

(*  Version  : [WM88] (equality) axioms. *)

(*  English  : The strong fixed point property holds for the set  *)

(*             P consisting of the combinators B, M and S, where ((Sx)y)z  *)

(*             = (xz)(yz), ((Bx)y)z = x(yz), Mx = xx. *)

(*  Refs     : [Smu85] Smullyan (1978), To Mock a Mocking Bird and Other Logi *)

(*           : [MW87]  McCune & Wos (1987), A Case Study in Automated Theorem *)

(*           : [WM88]  Wos & McCune (1988), Challenge Problems Focusing on Eq *)

(*           : [Wos89] Wos (1989), A Challenge Problem and a Recent Workshop *)

(*  Source   : [Wos89] *)

(*  Names    : - [Wos89] *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.33 v3.4.0, 0.50 v3.3.0, 0.57 v3.2.0, 0.64 v3.1.0, 0.67 v2.7.0, 0.55 v2.6.0, 0.17 v2.5.0, 0.25 v2.4.0, 0.00 v2.2.1, 0.67 v2.2.0, 0.71 v2.1.0, 1.00 v2.0.0 *)

(*  Syntax   : Number of clauses     :    4 (   0 non-Horn;   4 unit;   1 RR) *)

(*             Number of atoms       :    4 (   4 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    5 (   3 constant; 0-2 arity) *)

(*             Number of variables   :    8 (   0 singleton) *)

(*             Maximal term depth    :    4 (   3 average) *)

(*  Comments :  *)

(* -------------------------------------------------------------------------- *)
ntheorem prove_fixed_point:
 (∀Univ:Type.∀X:Univ.∀Y:Univ.∀Z:Univ.
∀apply:∀_:Univ.∀_:Univ.Univ.
∀b:Univ.
∀f:∀_:Univ.Univ.
∀m:Univ.
∀s:Univ.
∀H0:∀X:Univ.eq Univ (apply m X) (apply X X).
∀H1:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (apply (apply (apply b X) Y) Z) (apply X (apply Y Z)).
∀H2:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (apply (apply (apply s X) Y) Z) (apply (apply X Z) (apply Y Z)).∃Y:Univ.eq Univ (apply Y (f Y)) (apply (f Y) (apply Y (f Y))))
.
#Univ ##.
#X ##.
#Y ##.
#Z ##.
#apply ##.
#b ##.
#f ##.
#m ##.
#s ##.
#H0 ##.
#H1 ##.
#H2 ##.
napply (ex_intro ? ? ? ?) ##[
##2:
nauto by H0,H1,H2 ##;
##| ##skip ##]
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)

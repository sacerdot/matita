include "logic/equality.ma".

(* Inclusion of: COL049-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : COL049-1 : TPTP v3.7.0. Released v1.0.0. *)

(*  Domain   : Combinatory Logic *)

(*  Problem  : Strong fixed point for B, W, and M *)

(*  Version  : [WM88] (equality) axioms. *)

(*  English  : The strong fixed point property holds for the set  *)

(*             P consisting of the combinators B, W, and M, where ((Bx)y)z  *)

(*             = x(yz), (Wx)y = (xy)y, Mx = xx. *)

(*  Refs     : [Smu85] Smullyan (1978), To Mock a Mocking Bird and Other Logi *)

(*           : [MW87]  McCune & Wos (1987), A Case Study in Automated Theorem *)

(*           : [WM88]  Wos & McCune (1988), Challenge Problems Focusing on Eq *)

(*           : [Ove90] Overbeek (1990), ATP competition announced at CADE-10 *)

(*           : [LW92]  Lusk & Wos (1992), Benchmark Problems in Which Equalit *)

(*           : [Wos93] Wos (1993), The Kernel Strategy and Its Use for the St *)

(*           : [Ove93] Overbeek (1993), The CADE-11 Competitions: A Personal  *)

(*           : [LM93]  Lusk & McCune (1993), Uniform Strategies: The CADE-11  *)

(*           : [Zha93] Zhang (1993), Automated Proofs of Equality Problems in *)

(*  Source   : [Ove90] *)

(*  Names    : Problem 2 [WM88] *)

(*           : CADE-11 Competition Eq-6 [Ove90] *)

(*           : CL1 [LW92] *)

(*           : THEOREM EQ-6 [LM93] *)

(*           : Question 2 [Wos93] *)

(*           : PROBLEM 6 [Zha93] *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.22 v3.4.0, 0.25 v3.3.0, 0.29 v3.1.0, 0.44 v2.7.0, 0.27 v2.6.0, 0.17 v2.5.0, 0.25 v2.4.0, 0.00 v2.2.1, 0.22 v2.2.0, 0.14 v2.1.0, 0.62 v2.0.0 *)

(*  Syntax   : Number of clauses     :    4 (   0 non-Horn;   4 unit;   1 RR) *)

(*             Number of atoms       :    4 (   4 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    5 (   3 constant; 0-2 arity) *)

(*             Number of variables   :    7 (   0 singleton) *)

(*             Maximal term depth    :    4 (   3 average) *)

(*  Comments :  *)

(* -------------------------------------------------------------------------- *)
ntheorem prove_strong_fixed_point:
 (∀Univ:Type.∀X:Univ.∀Y:Univ.∀Z:Univ.
∀apply:∀_:Univ.∀_:Univ.Univ.
∀b:Univ.
∀f:∀_:Univ.Univ.
∀m:Univ.
∀w:Univ.
∀H0:∀X:Univ.eq Univ (apply m X) (apply X X).
∀H1:∀X:Univ.∀Y:Univ.eq Univ (apply (apply w X) Y) (apply (apply X Y) Y).
∀H2:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (apply (apply (apply b X) Y) Z) (apply X (apply Y Z)).∃Y:Univ.eq Univ (apply Y (f Y)) (apply (f Y) (apply Y (f Y))))
.
#Univ ##.
#X ##.
#Y ##.
#Z ##.
#apply ##.
#b ##.
#f ##.
#m ##.
#w ##.
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

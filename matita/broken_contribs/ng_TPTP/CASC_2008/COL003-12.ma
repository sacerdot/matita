include "logic/equality.ma".

(* Inclusion of: COL003-12.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : COL003-12 : TPTP v3.7.0. Released v2.1.0. *)

(*  Domain   : Combinatory Logic *)

(*  Problem  : Strong fixed point for B and W *)

(*  Version  : [WM88] (equality) axioms. *)

(*             Theorem formulation : The fixed point is provided and checked. *)

(*  English  : The strong fixed point property holds for the set  *)

(*             P consisting of the combinators B and W alone, where ((Bx)y)z  *)

(*             = x(yz) and (Wx)y = (xy)y. *)

(*  Refs     : [Smu85] Smullyan (1978), To Mock a Mocking Bird and Other Logi *)

(*           : [MW87]  McCune & Wos (1987), A Case Study in Automated Theorem *)

(*           : [WM88]  Wos & McCune (1988), Challenge Problems Focusing on Eq *)

(*           : [Wos93] Wos (1993), The Kernel Strategy and Its Use for the St *)

(*  Source   : [TPTP] *)

(*  Names    : J sage [MW87] *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.22 v3.4.0, 0.25 v3.3.0, 0.07 v3.1.0, 0.22 v2.7.0, 0.18 v2.6.0, 0.17 v2.5.0, 0.00 v2.2.1, 0.25 v2.2.0, 0.40 v2.1.0 *)

(*  Syntax   : Number of clauses     :    4 (   0 non-Horn;   4 unit;   2 RR) *)

(*             Number of atoms       :    4 (   4 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    5 (   4 constant; 0-2 arity) *)

(*             Number of variables   :    5 (   0 singleton) *)

(*             Maximal term depth    :    5 (   3 average) *)

(*  Comments : Found by Statman. *)

(* -------------------------------------------------------------------------- *)
ntheorem prove_strong_fixed_point:
 (∀Univ:Type.∀X:Univ.∀Y:Univ.∀Z:Univ.
∀apply:∀_:Univ.∀_:Univ.Univ.
∀b:Univ.
∀fixed_pt:Univ.
∀strong_fixed_point:Univ.
∀w:Univ.
∀H0:eq Univ strong_fixed_point (apply (apply b (apply w w)) (apply (apply b w) (apply (apply b b) b))).
∀H1:∀X:Univ.∀Y:Univ.eq Univ (apply (apply w X) Y) (apply (apply X Y) Y).
∀H2:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (apply (apply (apply b X) Y) Z) (apply X (apply Y Z)).eq Univ (apply strong_fixed_point fixed_pt) (apply fixed_pt (apply strong_fixed_point fixed_pt)))
.
#Univ ##.
#X ##.
#Y ##.
#Z ##.
#apply ##.
#b ##.
#fixed_pt ##.
#strong_fixed_point ##.
#w ##.
#H0 ##.
#H1 ##.
#H2 ##.
nauto by H0,H1,H2 ##;
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)

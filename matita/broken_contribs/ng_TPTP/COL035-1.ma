include "logic/equality.ma".

(* Inclusion of: COL035-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : COL035-1 : TPTP v3.7.0. Released v1.0.0. *)

(*  Domain   : Combinatory Logic *)

(*  Problem  : Strong fixed point for W, Q, and L *)

(*  Version  : [WM88] (equality) axioms. *)

(*  English  : The strong fixed point property holds for the set  *)

(*             P consisting of the combinators W, Q, and L, where (Lx)y  *)

(*             = x(yy), (Wx)y = (xy)y, ((Qx)y)z = y(xz). *)

(*  Refs     : [Smu85] Smullyan (1978), To Mock a Mocking Bird and Other Logi *)

(*           : [MW87]  McCune & Wos (1987), A Case Study in Automated Theorem *)

(*           : [WM88]  Wos & McCune (1988), Challenge Problems Focusing on Eq *)

(*           : [MW88]  McCune & Wos (1988), Some Fixed Point Problems in Comb *)

(*  Source   : [MW88] *)

(*  Names    : - [MW88] *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.11 v3.4.0, 0.12 v3.3.0, 0.21 v3.2.0, 0.14 v3.1.0, 0.22 v2.7.0, 0.09 v2.6.0, 0.17 v2.5.0, 0.00 v2.2.1, 0.11 v2.2.0, 0.00 v2.1.0, 0.25 v2.0.0 *)

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
∀f:∀_:Univ.Univ.
∀l:Univ.
∀q:Univ.
∀w:Univ.
∀H0:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (apply (apply (apply q X) Y) Z) (apply Y (apply X Z)).
∀H1:∀X:Univ.∀Y:Univ.eq Univ (apply (apply w X) Y) (apply (apply X Y) Y).
∀H2:∀X:Univ.∀Y:Univ.eq Univ (apply (apply l X) Y) (apply X (apply Y Y)).∃Y:Univ.eq Univ (apply Y (f Y)) (apply (f Y) (apply Y (f Y))))
.
#Univ ##.
#X ##.
#Y ##.
#Z ##.
#apply ##.
#f ##.
#l ##.
#q ##.
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

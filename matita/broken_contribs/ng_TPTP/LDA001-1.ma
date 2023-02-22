include "logic/equality.ma".

(* Inclusion of: LDA001-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : LDA001-1 : TPTP v3.7.0. Released v1.0.0. *)

(*  Domain   : LD-Algebras *)

(*  Problem  : Verify 3*2*U = UUU, where U = 2*2 *)

(*  Version  : [Jec93] (equality) axioms. *)

(*  English  :  *)

(*  Refs     : [Jec93] Jech (1993), LD-Algebras *)

(*  Source   : [Jec93] *)

(*  Names    : Problem 1 [Jec93] *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.00 v2.2.1, 0.22 v2.2.0, 0.29 v2.1.0, 0.25 v2.0.0 *)

(*  Syntax   : Number of clauses     :    5 (   0 non-Horn;   5 unit;   4 RR) *)

(*             Number of atoms       :    5 (   5 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    5 (   4 constant; 0-2 arity) *)

(*             Number of variables   :    3 (   0 singleton) *)

(*             Maximal term depth    :    3 (   2 average) *)

(*  Comments :  *)

(* -------------------------------------------------------------------------- *)

(* ----A1: x(yz)=xy(xz)  *)

(* ----3*2*U = U*U*U  *)
ntheorem prove_equation:
 (∀Univ:Type.∀X:Univ.∀Y:Univ.∀Z:Univ.
∀f:∀_:Univ.∀_:Univ.Univ.
∀n1:Univ.
∀n2:Univ.
∀n3:Univ.
∀u:Univ.
∀H0:eq Univ u (f n2 n2).
∀H1:eq Univ n3 (f n2 n1).
∀H2:eq Univ n2 (f n1 n1).
∀H3:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (f X (f Y Z)) (f (f X Y) (f X Z)).eq Univ (f (f n3 n2) u) (f (f u u) u))
.
#Univ ##.
#X ##.
#Y ##.
#Z ##.
#f ##.
#n1 ##.
#n2 ##.
#n3 ##.
#u ##.
#H0 ##.
#H1 ##.
#H2 ##.
#H3 ##.
nauto by H0,H1,H2,H3 ##;
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)

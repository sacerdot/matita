include "logic/equality.ma".

(* Inclusion of: LDA002-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : LDA002-1 : TPTP v3.7.0. Released v1.0.0. *)

(*  Domain   : LD-Algebras *)

(*  Problem  : Verify 3*2(U2)(UU(UU)) = U1(U3)(UU(UU)) *)

(*  Version  : [Jec93] (equality) axioms. *)

(*  English  :  *)

(*  Refs     : [Jec93] Jech (1993), LD-Algebras *)

(*  Source   : [Jec93] *)

(*  Names    : Problem 2 [Jec93] *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.11 v3.4.0, 0.12 v3.3.0, 0.00 v2.2.1, 0.22 v2.2.0, 0.29 v2.1.0, 0.38 v2.0.0 *)

(*  Syntax   : Number of clauses     :   12 (   0 non-Horn;  12 unit;  11 RR) *)

(*             Number of atoms       :   12 (  12 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :   12 (  11 constant; 0-2 arity) *)

(*             Number of variables   :    3 (   0 singleton) *)

(*             Maximal term depth    :    3 (   2 average) *)

(*  Comments :  *)

(* -------------------------------------------------------------------------- *)

(* ----A1: x(yz)=xy(xz)  *)

(* ----3*2*U2*(UU*UU) = U1*U3*(uU*UU)  *)
ntheorem prove_equation:
 (∀Univ:Type.∀X:Univ.∀Y:Univ.∀Z:Univ.
∀a:Univ.
∀b:Univ.
∀f:∀_:Univ.∀_:Univ.Univ.
∀n1:Univ.
∀n2:Univ.
∀n3:Univ.
∀u:Univ.
∀u1:Univ.
∀u2:Univ.
∀u3:Univ.
∀uu:Univ.
∀v:Univ.
∀H0:eq Univ v (f uu uu).
∀H1:eq Univ b (f u1 u3).
∀H2:eq Univ a (f (f n3 n2) u2).
∀H3:eq Univ uu (f u u).
∀H4:eq Univ u3 (f u n3).
∀H5:eq Univ u2 (f u n2).
∀H6:eq Univ u1 (f u n1).
∀H7:eq Univ u (f n2 n2).
∀H8:eq Univ n3 (f n2 n1).
∀H9:eq Univ n2 (f n1 n1).
∀H10:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (f X (f Y Z)) (f (f X Y) (f X Z)).eq Univ (f a v) (f b v))
.
#Univ ##.
#X ##.
#Y ##.
#Z ##.
#a ##.
#b ##.
#f ##.
#n1 ##.
#n2 ##.
#n3 ##.
#u ##.
#u1 ##.
#u2 ##.
#u3 ##.
#uu ##.
#v ##.
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

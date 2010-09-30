include "logic/equality.ma".

(* Inclusion of: LDA007-3.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : LDA007-3 : TPTP v3.7.0. Released v1.0.0. *)

(*  Domain   : LD-Algebras (Embedding algebras) *)

(*  Problem  : Let g = cr(t). Show that t(tsg) = tt(ts)(tg)  *)

(*  Version  : [Jec93] axioms : Incomplete > Reduced & Augmented > Incomplete. *)

(*  English  :  *)

(*  Refs     : [Jec93] Jech (1993), LD-Algebras *)

(*  Source   : [Jec93] *)

(*  Names    : Problem 8 [Jec93] *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.00 v2.2.1, 0.11 v2.2.0, 0.14 v2.1.0, 0.13 v2.0.0 *)

(*  Syntax   : Number of clauses     :    7 (   0 non-Horn;   7 unit;   6 RR) *)

(*             Number of atoms       :    7 (   7 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    9 (   8 constant; 0-2 arity) *)

(*             Number of variables   :    3 (   0 singleton) *)

(*             Maximal term depth    :    3 (   2 average) *)

(*  Comments :  *)

(* -------------------------------------------------------------------------- *)

(* ----Include Embedding algebra axioms  *)

(*  include('Axioms/LDA001-0.ax'). *)

(* -------------------------------------------------------------------------- *)

(* ----t(tsk) = tt(ts)(tk), where k=crit(t)  *)
ntheorem prove_equation:
 (∀Univ:Type.∀X:Univ.∀Y:Univ.∀Z:Univ.
∀f:∀_:Univ.∀_:Univ.Univ.
∀k:Univ.
∀s:Univ.
∀t:Univ.
∀tk:Univ.
∀ts:Univ.
∀tsk:Univ.
∀tt:Univ.
∀tt_ts:Univ.
∀H0:eq Univ tsk (f ts k).
∀H1:eq Univ tk (f t k).
∀H2:eq Univ tt_ts (f tt ts).
∀H3:eq Univ ts (f t s).
∀H4:eq Univ tt (f t t).
∀H5:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (f X (f Y Z)) (f (f X Y) (f X Z)).eq Univ (f t tsk) (f tt_ts tk))
.
#Univ ##.
#X ##.
#Y ##.
#Z ##.
#f ##.
#k ##.
#s ##.
#t ##.
#tk ##.
#ts ##.
#tsk ##.
#tt ##.
#tt_ts ##.
#H0 ##.
#H1 ##.
#H2 ##.
#H3 ##.
#H4 ##.
#H5 ##.
nauto by H0,H1,H2,H3,H4,H5 ##;
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)

include "logic/equality.ma".

(* Inclusion of: SYN305-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : SYN305-1 : TPTP v3.7.0. Released v1.2.0. *)

(*  Domain   : Syntactic *)

(*  Problem  : Problem for testing satisfiability *)

(*  Version  : Especial. *)

(*  English  :  *)

(*  Refs     : [BCP94] Bourely et al. (1994), A Method for Building Models Au *)

(*  Source   : [BCP94] *)

(*  Names    : Example 3 [BCP94] *)

(*  Status   : Satisfiable *)

(*  Rating   : 0.67 v2.4.0, 0.33 v2.2.1, 0.25 v2.2.0, 0.67 v2.1.0, 0.00 v2.0.0 *)

(*  Syntax   : Number of clauses     :    3 (   0 non-Horn;   3 unit;   1 RR) *)

(*             Number of atoms       :    3 (   3 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    3 (   0 constant; 1-1 arity) *)

(*             Number of variables   :    3 (   0 singleton) *)

(*             Maximal term depth    :    3 (   2 average) *)

(*  Comments :  *)

(* -------------------------------------------------------------------------- *)
ntheorem clause3:
 (∀Univ:Type.∀X:Univ.
∀f:∀_:Univ.Univ.
∀g1:∀_:Univ.Univ.
∀g2:∀_:Univ.Univ.
∀H0:∀X:Univ.eq Univ (f (g2 X)) X.
∀H1:∀X:Univ.eq Univ (f (g1 X)) X.∃X:Univ.eq Univ (g1 X) (g2 X))
.
#Univ ##.
#X ##.
#f ##.
#g1 ##.
#g2 ##.
#H0 ##.
#H1 ##.
napply (ex_intro ? ? ? ?) ##[
##2:
nauto by H0,H1 ##;
##| ##skip ##]
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)

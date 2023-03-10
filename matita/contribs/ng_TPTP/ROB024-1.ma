include "logic/equality.ma".

(* Inclusion of: ROB024-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : ROB024-1 : TPTP v3.7.0. Released v1.0.0. *)

(*  Domain   : Robbins Algebra *)

(*  Problem  : -(a + (a + b)) + -(a + -b) = a => Boolean *)

(*  Version  : [Win90] (equality) axioms. *)

(*  English  : If there exist a and b so that -(a + (a + b)) + -(a + -b)  *)

(*             = a then the algebra is Boolean. *)

(*  Refs     : [Win90] Winker (1990), Robbins Algebra: Conditions that make a *)

(*           : [WW+90] Wos et al. (1990), Automated Reasoning Contributes to  *)

(*  Source   : [WW+90] *)

(*  Names    : RA-1 [WW+90] *)

(*  Status   : Unknown *)

(*  Rating   : 1.00 v2.0.0 *)

(*  Syntax   : Number of clauses     :    5 (   0 non-Horn;   5 unit;   2 RR) *)

(*             Number of atoms       :    5 (   5 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    4 (   2 constant; 0-2 arity) *)

(*             Number of variables   :    7 (   0 singleton) *)

(*             Maximal term depth    :    6 (   3 average) *)

(*  Comments : Commutativity, associativity, and Huntington's axiom  *)

(*             axiomatize Boolean algebra. *)

(* -------------------------------------------------------------------------- *)

(* ----Include axioms for Robbins algebra  *)

(* Inclusion of: Axioms/ROB001-0.ax *)

(* -------------------------------------------------------------------------- *)

(*  File     : ROB001-0 : TPTP v3.7.0. Released v1.0.0. *)

(*  Domain   : Robbins algebra *)

(*  Axioms   : Robbins algebra axioms *)

(*  Version  : [Win90] (equality) axioms. *)

(*  English  :  *)

(*  Refs     : [HMT71] Henkin et al. (1971), Cylindrical Algebras *)

(*           : [Win90] Winker (1990), Robbins Algebra: Conditions that make a *)

(*  Source   : [OTTER] *)

(*  Names    : Lemma 2.2 [Win90] *)

(*  Status   :  *)

(*  Syntax   : Number of clauses    :    3 (   0 non-Horn;   3 unit;   0 RR) *)

(*             Number of atoms      :    3 (   3 equality) *)

(*             Maximal clause size  :    1 (   1 average) *)

(*             Number of predicates :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors   :    2 (   0 constant; 1-2 arity) *)

(*             Number of variables  :    7 (   0 singleton) *)

(*             Maximal term depth   :    6 (   3 average) *)

(*  Comments :  *)

(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
ntheorem prove_huntingtons_axiom:
 (???Univ:Type.???X:Univ.???Y:Univ.???Z:Univ.
???a:Univ.
???add:???_:Univ.???_:Univ.Univ.
???b:Univ.
???negate:???_:Univ.Univ.
???H0:eq Univ (negate (add (negate (add a (add a b))) (negate (add a (negate b))))) a.
???H1:???X:Univ.???Y:Univ.eq Univ (negate (add (negate (add X Y)) (negate (add X (negate Y))))) X.
???H2:???X:Univ.???Y:Univ.???Z:Univ.eq Univ (add (add X Y) Z) (add X (add Y Z)).
???H3:???X:Univ.???Y:Univ.eq Univ (add X Y) (add Y X).eq Univ (add (negate (add a (negate b))) (negate (add (negate a) (negate b)))) b)
.
#Univ ##.
#X ##.
#Y ##.
#Z ##.
#a ##.
#add ##.
#b ##.
#negate ##.
#H0 ##.
#H1 ##.
#H2 ##.
#H3 ##.
nauto by H0,H1,H2,H3 ##;
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)

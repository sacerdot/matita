include "logic/equality.ma".

(* Inclusion of: ROB026-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : ROB026-1 : TPTP v3.7.0. Released v1.2.0. *)

(*  Domain   : Robbins Algebra *)

(*  Problem  : c + d = c => Boolean *)

(*  Version  : [Win90] (equality) axioms. *)

(*             Theorem formulation : Denies Huntington's axiom. *)

(*  English  : If there are elements c and d such that c+d=d, then the  *)

(*             algebra is Boolean. *)

(*  Refs     : [HMT71] Henkin et al. (1971), Cylindrical Algebras *)

(*           : [Win90] Winker (1990), Robbins Algebra: Conditions that make a *)

(*           : [Wos94] Wos (1994), Two Challenge Problems *)

(*  Source   : [Wos94] *)

(*  Names    : - [Wos94] *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.78 v3.4.0, 0.88 v3.3.0, 0.86 v3.1.0, 0.89 v2.7.0, 0.91 v2.6.0, 0.83 v2.5.0, 0.75 v2.4.0, 0.67 v2.3.0, 1.00 v2.0.0 *)

(*  Syntax   : Number of clauses     :    5 (   0 non-Horn;   5 unit;   2 RR) *)

(*             Number of atoms       :    5 (   5 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    6 (   4 constant; 0-2 arity) *)

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
???c:Univ.
???d:Univ.
???negate:???_:Univ.Univ.
???H0:eq Univ (add c d) c.
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
#c ##.
#d ##.
#negate ##.
#H0 ##.
#H1 ##.
#H2 ##.
#H3 ##.
nauto by H0,H1,H2,H3 ##;
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)

include "logic/equality.ma".

(* Inclusion of: ROB032-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : ROB032-1 : TPTP v3.7.0. Released v3.1.0. *)

(*  Domain   : Robbins Algebra *)

(*  Problem  : Robbins => Exists absorbed element *)

(*  Version  : [Win90] (equality) axioms. *)

(*             Theorem formulation : Denies Huntington's axiom. *)

(*  English  : If there are elements c and d such that c+d=d, then the  *)

(*             algebra is Boolean. *)

(*  Refs     : [Win90] Winker (1990), Robbins Algebra: Conditions that make a *)

(*           : [Wos92] Wos (1992), An Opportunity to Test Your Skills, and th *)

(*           : [Loe04] Loechner (2004), Email to Geoff Sutcliffe *)

(*  Source   : [Loe04] *)

(*  Names    :  *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 1.00 v3.1.0 *)

(*  Syntax   : Number of clauses     :    4 (   0 non-Horn;   4 unit;   1 RR) *)

(*             Number of atoms       :    4 (   4 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    2 (   0 constant; 1-2 arity) *)

(*             Number of variables   :    9 (   1 singleton) *)

(*             Maximal term depth    :    6 (   2 average) *)

(*  Comments :  *)

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
ntheorem prove_absorbtion:
 (???Univ:Type.???C:Univ.???D:Univ.???X:Univ.???Y:Univ.???Z:Univ.
???add:???_:Univ.???_:Univ.Univ.
???negate:???_:Univ.Univ.
???H0:???X:Univ.???Y:Univ.eq Univ (negate (add (negate (add X Y)) (negate (add X (negate Y))))) X.
???H1:???X:Univ.???Y:Univ.???Z:Univ.eq Univ (add (add X Y) Z) (add X (add Y Z)).
???H2:???X:Univ.???Y:Univ.eq Univ (add X Y) (add Y X).???C:Univ.???D:Univ.eq Univ (add C D) D)
.
#Univ ##.
#C ##.
#D ##.
#X ##.
#Y ##.
#Z ##.
#add ##.
#negate ##.
#H0 ##.
#H1 ##.
#H2 ##.
napply (ex_intro ? ? ? ?) ##[
##2:
napply (ex_intro ? ? ? ?) ##[
##2:
nauto by H0,H1,H2 ##;
##| ##skip ##]
##| ##skip ##]
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)


include "logic/equality.ma".
(* Inclusion of: LCL164-1.p *)
(* -------------------------------------------------------------------------- *)
(*  File     : LCL164-1 : TPTP v3.1.1. Released v1.0.0. *)
(*  Domain   : Logic Calculi (Wajsberg Algebra) *)
(*  Problem  : The 4th Wajsberg algebra axiom, from the alternative axioms *)
(*  Version  : [Bon91] (equality) axioms. *)
(*  English  :  *)
(*  Refs     : [FRT84] Font et al. (1984), Wajsberg Algebras *)
(*           : [AB90]  Anantharaman & Bonacina (1990), An Application of the  *)
(*           : [Bon91] Bonacina (1991), Problems in Lukasiewicz Logic *)
(*  Source   : [Bon91] *)
(*  Names    : W axiom 4 [Bon91] *)
(*  Status   : Unsatisfiable *)
(*  Rating   : 0.00 v2.2.1, 0.22 v2.2.0, 0.29 v2.1.0, 0.38 v2.0.0 *)
(*  Syntax   : Number of clauses     :   14 (   0 non-Horn;  14 unit;   2 RR) *)
(*             Number of atoms       :   14 (  14 equality) *)
(*             Maximal clause size   :    1 (   1 average) *)
(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)
(*             Number of functors    :    8 (   4 constant; 0-2 arity) *)
(*             Number of variables   :   19 (   1 singleton) *)
(*             Maximal term depth    :    5 (   2 average) *)
(*  Comments :  *)
(* -------------------------------------------------------------------------- *)
(* ----Include Alternative Wajsberg algebra axioms  *)
(* Inclusion of: Axioms/LCL002-0.ax *)
(* -------------------------------------------------------------------------- *)
(*  File     : LCL002-0 : TPTP v3.1.1. Released v1.0.0. *)
(*  Domain   : Logic Calculi (Wajsberg Algebras) *)
(*  Axioms   : Alternative Wajsberg algebra axioms *)
(*  Version  : [AB90] (equality) axioms. *)
(*  English  :  *)
(*  Refs     : [FRT84] Font et al. (1984), Wajsberg Algebras *)
(*           : [AB90]  Anantharaman & Bonacina (1990), An Application of the  *)
(*           : [Bon91] Bonacina (1991), Problems in Lukasiewicz Logic *)
(*  Source   : [Bon91] *)
(*  Names    :  *)
(*  Status   :  *)
(*  Syntax   : Number of clauses    :    8 (   0 non-Horn;   8 unit;   0 RR) *)
(*             Number of literals   :    8 (   8 equality) *)
(*             Maximal clause size  :    1 (   1 average) *)
(*             Number of predicates :    1 (   0 propositional; 2-2 arity) *)
(*             Number of functors   :    5 (   2 constant; 0-2 arity) *)
(*             Number of variables  :   10 (   1 singleton) *)
(*             Maximal term depth   :    5 (   2 average) *)
(*  Comments : To be used in conjunction with the LAT003 alternative  *)
(*             Wajsberg algebra definitions. *)
(* -------------------------------------------------------------------------- *)
(* -------------------------------------------------------------------------- *)
(* -------------------------------------------------------------------------- *)
(* ----Include some Alternative Wajsberg algebra definitions  *)
(*  include('Axioms/LCL002-1.ax'). *)
(* ----Definition that and_star is AC and xor is C  *)
(* ----Definition of false in terms of true  *)
(* ----Include the definition of implies in terms of xor and and_star  *)
theorem prove_wajsberg_axiom:
 \forall Univ:Set.
\forall and_star:\forall _:Univ.\forall _:Univ.Univ.
\forall falsehood:Univ.
\forall implies:\forall _:Univ.\forall _:Univ.Univ.
\forall not:\forall _:Univ.Univ.
\forall truth:Univ.
\forall x:Univ.
\forall xor:\forall _:Univ.\forall _:Univ.Univ.
\forall y:Univ.
\forall H0:\forall X:Univ.\forall Y:Univ.eq Univ (implies X Y) (xor truth (and_star X (xor truth Y))).
\forall H1:eq Univ (not truth) falsehood.
\forall H2:\forall X:Univ.\forall Y:Univ.eq Univ (and_star X Y) (and_star Y X).
\forall H3:\forall X:Univ.\forall Y:Univ.\forall Z:Univ.eq Univ (and_star (and_star X Y) Z) (and_star X (and_star Y Z)).
\forall H4:\forall X:Univ.\forall Y:Univ.eq Univ (xor X Y) (xor Y X).
\forall H5:\forall X:Univ.\forall Y:Univ.eq Univ (and_star (xor (and_star (xor truth X) Y) truth) Y) (and_star (xor (and_star (xor truth Y) X) truth) X).
\forall H6:\forall X:Univ.\forall Y:Univ.eq Univ (xor X (xor truth Y)) (xor (xor X truth) Y).
\forall H7:\forall X:Univ.eq Univ (and_star (xor truth X) X) falsehood.
\forall H8:\forall X:Univ.eq Univ (and_star X falsehood) falsehood.
\forall H9:\forall X:Univ.eq Univ (and_star X truth) X.
\forall H10:\forall X:Univ.eq Univ (xor X X) falsehood.
\forall H11:\forall X:Univ.eq Univ (xor X falsehood) X.
\forall H12:\forall X:Univ.eq Univ (not X) (xor X truth).eq Univ (implies (implies (not x) (not y)) (implies y x)) truth
.
intros.
autobatch paramodulation timeout=100;
try assumption.
print proofterm.
qed.
(* -------------------------------------------------------------------------- *)

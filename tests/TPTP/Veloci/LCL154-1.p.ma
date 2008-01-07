
include "logic/equality.ma".
(* Inclusion of: LCL154-1.p *)
(* -------------------------------------------------------------------------- *)
(*  File     : LCL154-1 : TPTP v3.1.1. Released v1.0.0. *)
(*  Domain   : Logic Calculi (Wajsberg Algebra) *)
(*  Problem  : The 2nd alternative Wajsberg algebra axiom *)
(*  Version  : [Bon91] (equality) axioms. *)
(*  English  :  *)
(*  Refs     : [FRT84] Font et al. (1984), Wajsberg Algebras *)
(*           : [AB90]  Anantharaman & Bonacina (1990), An Application of the  *)
(*           : [Bon91] Bonacina (1991), Problems in Lukasiewicz Logic *)
(*  Source   : [Bon91] *)
(*  Names    : W' axiom 2 [Bon91] *)
(*  Status   : Unsatisfiable *)
(*  Rating   : 0.00 v2.2.1, 0.22 v2.2.0, 0.29 v2.1.0, 0.38 v2.0.0 *)
(*  Syntax   : Number of clauses     :   17 (   0 non-Horn;  17 unit;   2 RR) *)
(*             Number of atoms       :   17 (  17 equality) *)
(*             Maximal clause size   :    1 (   1 average) *)
(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)
(*             Number of functors    :    9 (   3 constant; 0-2 arity) *)
(*             Number of variables   :   33 (   0 singleton) *)
(*             Maximal term depth    :    4 (   2 average) *)
(*  Comments :  *)
(* -------------------------------------------------------------------------- *)
(* ----Include Wajsberg algebra axioms  *)
(* Inclusion of: Axioms/LCL001-0.ax *)
(* -------------------------------------------------------------------------- *)
(*  File     : LCL001-0 : TPTP v3.1.1. Released v1.0.0. *)
(*  Domain   : Logic Calculi (Wajsberg Algebras) *)
(*  Axioms   : Wajsberg algebra axioms *)
(*  Version  : [Bon91] (equality) axioms. *)
(*  English  :  *)
(*  Refs     : [FRT84] Font et al. (1984), Wajsberg Algebras *)
(*           : [Bon91] Bonacina (1991), Problems in Lukasiewicz Logic *)
(*           : [MW92]  McCune & Wos (1992), Experiments in Automated Deductio *)
(*  Source   : [MW92] *)
(*  Names    : MV Sentential Calculus [MW92] *)
(*  Status   :  *)
(*  Syntax   : Number of clauses    :    4 (   0 non-Horn;   4 unit;   0 RR) *)
(*             Number of literals   :    4 (   4 equality) *)
(*             Maximal clause size  :    1 (   1 average) *)
(*             Number of predicates :    1 (   0 propositional; 2-2 arity) *)
(*             Number of functors   :    3 (   1 constant; 0-2 arity) *)
(*             Number of variables  :    8 (   0 singleton) *)
(*             Maximal term depth   :    4 (   2 average) *)
(*  Comments :  *)
(* -------------------------------------------------------------------------- *)
(* -------------------------------------------------------------------------- *)
(* ----Include Wajsberg algebra and and or definitions  *)
(* Inclusion of: Axioms/LCL001-2.ax *)
(* -------------------------------------------------------------------------- *)
(*  File     : LCL001-2 : TPTP v3.1.1. Released v1.0.0. *)
(*  Domain   : Logic Calculi (Wajsberg Algebras) *)
(*  Axioms   : Wajsberg algebra AND and OR definitions *)
(*  Version  : [AB90] (equality) axioms. *)
(*  English  :  *)
(*  Refs     : [FRT84] Font et al. (1984), Wajsberg Algebras *)
(*           : [AB90]  Anantharaman & Bonacina (1990), An Application of the  *)
(*           : [Bon91] Bonacina (1991), Problems in Lukasiewicz Logic *)
(*  Source   : [Bon91] *)
(*  Names    :  *)
(*  Status   :  *)
(*  Syntax   : Number of clauses    :    6 (   0 non-Horn;   6 unit;   0 RR) *)
(*             Number of literals   :    6 (   6 equality) *)
(*             Maximal clause size  :    1 (   1 average) *)
(*             Number of predicates :    1 (   0 propositional; 2-2 arity) *)
(*             Number of functors   :    4 (   0 constant; 1-2 arity) *)
(*             Number of variables  :   14 (   0 singleton) *)
(*             Maximal term depth   :    4 (   3 average) *)
(*  Comments : Requires LCL001-0.ax *)
(* -------------------------------------------------------------------------- *)
(* ----Definitions of or and and, which are AC  *)
(* -------------------------------------------------------------------------- *)
(* ----Include Alternative Wajsberg algebra definitions  *)
(* Inclusion of: Axioms/LCL002-1.ax *)
(* -------------------------------------------------------------------------- *)
(*  File     : LCL002-1 : TPTP v3.1.1. Released v1.0.0. *)
(*  Domain   : Logic Calculi (Wajsberg Algebras) *)
(*  Axioms   : Alternative Wajsberg algebra definitions *)
(*  Version  : [AB90] (equality) axioms. *)
(*  English  :  *)
(*  Refs     : [FRT84] Font et al. (1984), Wajsberg Algebras *)
(*           : [AB90]  Anantharaman & Bonacina (1990), An Application of the  *)
(*           : [Bon91] Bonacina (1991), Problems in Lukasiewicz Logic *)
(*  Source   : [Bon91] *)
(*  Names    :  *)
(*  Status   :  *)
(*  Syntax   : Number of clauses    :    6 (   0 non-Horn;   6 unit;   1 RR) *)
(*             Number of literals   :    6 (   6 equality) *)
(*             Maximal clause size  :    1 (   1 average) *)
(*             Number of predicates :    1 (   0 propositional; 2-2 arity) *)
(*             Number of functors   :    7 (   2 constant; 0-2 arity) *)
(*             Number of variables  :   11 (   0 singleton) *)
(*             Maximal term depth   :    4 (   2 average) *)
(*  Comments : Requires LCL001-0.ax LCL001-2.ax *)
(* -------------------------------------------------------------------------- *)
(* ----Definitions of and_star and xor, where and_star is AC and xor is C  *)
(* ---I guess the next two can be derived from the AC of and *)
(* ----Definition of false in terms of truth  *)
(* -------------------------------------------------------------------------- *)
(* -------------------------------------------------------------------------- *)
theorem prove_alternative_wajsberg_axiom:
 \forall Univ:Set.
\forall myand:\forall _:Univ.\forall _:Univ.Univ.
\forall and_star:\forall _:Univ.\forall _:Univ.Univ.
\forall falsehood:Univ.
\forall implies:\forall _:Univ.\forall _:Univ.Univ.
\forall not:\forall _:Univ.Univ.
\forall or:\forall _:Univ.\forall _:Univ.Univ.
\forall truth:Univ.
\forall x:Univ.
\forall xor:\forall _:Univ.\forall _:Univ.Univ.
\forall H0:eq Univ (not truth) falsehood.
\forall H1:\forall X:Univ.\forall Y:Univ.eq Univ (and_star X Y) (and_star Y X).
\forall H2:\forall X:Univ.\forall Y:Univ.\forall Z:Univ.eq Univ (and_star (and_star X Y) Z) (and_star X (and_star Y Z)).
\forall H3:\forall X:Univ.\forall Y:Univ.eq Univ (and_star X Y) (not (or (not X) (not Y))).
\forall H4:\forall X:Univ.\forall Y:Univ.eq Univ (xor X Y) (xor Y X).
\forall H5:\forall X:Univ.\forall Y:Univ.eq Univ (xor X Y) (or (myand X (not Y)) (myand (not X) Y)).
\forall H6:\forall X:Univ.\forall Y:Univ.eq Univ (myand X Y) (myand Y X).
\forall H7:\forall X:Univ.\forall Y:Univ.\forall Z:Univ.eq Univ (myand (myand X Y) Z) (myand X (myand Y Z)).
\forall H8:\forall X:Univ.\forall Y:Univ.eq Univ (myand X Y) (not (or (not X) (not Y))).
\forall H9:\forall X:Univ.\forall Y:Univ.eq Univ (or X Y) (or Y X).
\forall H10:\forall X:Univ.\forall Y:Univ.\forall Z:Univ.eq Univ (or (or X Y) Z) (or X (or Y Z)).
\forall H11:\forall X:Univ.\forall Y:Univ.eq Univ (or X Y) (implies (not X) Y).
\forall H12:\forall X:Univ.\forall Y:Univ.eq Univ (implies (implies (not X) (not Y)) (implies Y X)) truth.
\forall H13:\forall X:Univ.\forall Y:Univ.eq Univ (implies (implies X Y) Y) (implies (implies Y X) X).
\forall H14:\forall X:Univ.\forall Y:Univ.\forall Z:Univ.eq Univ (implies (implies X Y) (implies (implies Y Z) (implies X Z))) truth.
\forall H15:\forall X:Univ.eq Univ (implies truth X) X.eq Univ (xor x falsehood) x
.
intros.
autobatch paramodulation timeout=100;
try assumption.
print proofterm.
qed.
(* -------------------------------------------------------------------------- *)

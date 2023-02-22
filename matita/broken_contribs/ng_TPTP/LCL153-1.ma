include "logic/equality.ma".

(* Inclusion of: LCL153-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : LCL153-1 : TPTP v3.7.0. Released v1.0.0. *)

(*  Domain   : Logic Calculi (Wajsberg Algebra) *)

(*  Problem  : The 1st alternative Wajsberg algebra axiom *)

(*  Version  : [Bon91] (equality) axioms. *)

(*  English  :  *)

(*  Refs     : [FRT84] Font et al. (1984), Wajsberg Algebras *)

(*           : [AB90]  Anantharaman & Bonacina (1990), An Application of the  *)

(*           : [Bon91] Bonacina (1991), Problems in Lukasiewicz Logic *)

(*  Source   : [Bon91] *)

(*  Names    : W' axiom 1 [Bon91] *)

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

(*  File     : LCL001-0 : TPTP v3.7.0. Released v1.0.0. *)

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

(*             Number of atoms      :    4 (   4 equality) *)

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

(*  File     : LCL001-2 : TPTP v3.7.0. Released v1.0.0. *)

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

(*             Number of atoms      :    6 (   6 equality) *)

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

(*  File     : LCL002-1 : TPTP v3.7.0. Released v1.0.0. *)

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

(*             Number of atoms      :    6 (   6 equality) *)

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
ntheorem prove_alternative_wajsberg_axiom:
 (∀Univ:Type.∀X:Univ.∀Y:Univ.∀Z:Univ.
∀myand:∀_:Univ.∀_:Univ.Univ.
∀and_star:∀_:Univ.∀_:Univ.Univ.
∀falsehood:Univ.
∀implies:∀_:Univ.∀_:Univ.Univ.
∀not:∀_:Univ.Univ.
∀or:∀_:Univ.∀_:Univ.Univ.
∀truth:Univ.
∀x:Univ.
∀xor:∀_:Univ.∀_:Univ.Univ.
∀H0:eq Univ (not truth) falsehood.
∀H1:∀X:Univ.∀Y:Univ.eq Univ (and_star X Y) (and_star Y X).
∀H2:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (and_star (and_star X Y) Z) (and_star X (and_star Y Z)).
∀H3:∀X:Univ.∀Y:Univ.eq Univ (and_star X Y) (not (or (not X) (not Y))).
∀H4:∀X:Univ.∀Y:Univ.eq Univ (xor X Y) (xor Y X).
∀H5:∀X:Univ.∀Y:Univ.eq Univ (xor X Y) (or (myand X (not Y)) (myand (not X) Y)).
∀H6:∀X:Univ.∀Y:Univ.eq Univ (myand X Y) (myand Y X).
∀H7:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (myand (myand X Y) Z) (myand X (myand Y Z)).
∀H8:∀X:Univ.∀Y:Univ.eq Univ (myand X Y) (not (or (not X) (not Y))).
∀H9:∀X:Univ.∀Y:Univ.eq Univ (or X Y) (or Y X).
∀H10:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (or (or X Y) Z) (or X (or Y Z)).
∀H11:∀X:Univ.∀Y:Univ.eq Univ (or X Y) (implies (not X) Y).
∀H12:∀X:Univ.∀Y:Univ.eq Univ (implies (implies (not X) (not Y)) (implies Y X)) truth.
∀H13:∀X:Univ.∀Y:Univ.eq Univ (implies (implies X Y) Y) (implies (implies Y X) X).
∀H14:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (implies (implies X Y) (implies (implies Y Z) (implies X Z))) truth.
∀H15:∀X:Univ.eq Univ (implies truth X) X.eq Univ (not x) (xor x truth))
.
#Univ ##.
#X ##.
#Y ##.
#Z ##.
#myand ##.
#and_star ##.
#falsehood ##.
#implies ##.
#not ##.
#or ##.
#truth ##.
#x ##.
#xor ##.
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
#H11 ##.
#H12 ##.
#H13 ##.
#H14 ##.
#H15 ##.
nauto by H0,H1,H2,H3,H4,H5,H6,H7,H8,H9,H10,H11,H12,H13,H14,H15 ##;
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)

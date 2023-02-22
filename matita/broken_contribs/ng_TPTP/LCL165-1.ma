include "logic/equality.ma".

(* Inclusion of: LCL165-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : LCL165-1 : TPTP v3.7.0. Released v1.0.0. *)

(*  Domain   : Logic Calculi (Wajsberg Algebra) *)

(*  Problem  : A ntheorem in Wajsberg algebras *)

(*  Version  : [Bon91] (equality) axioms. *)

(*  English  :  *)

(*  Refs     : [FRT84] Font et al. (1984), Wajsberg Algebras *)

(*           : [AB90]  Anantharaman & Bonacina (1990), An Application of the  *)

(*           : [Bon91] Bonacina (1991), Problems in Lukasiewicz Logic *)

(*  Source   : [Bon91] *)

(*  Names    : Third problem [Bon91] *)

(*  Status   : Satisfiable *)

(*  Rating   : 0.33 v3.2.0, 0.67 v3.1.0, 0.33 v2.5.0, 0.67 v2.4.0, 1.00 v2.0.0 *)

(*  Syntax   : Number of clauses     :   11 (   0 non-Horn;  11 unit;   1 RR) *)

(*             Number of atoms       :   11 (  11 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    6 (   2 constant; 0-2 arity) *)

(*             Number of variables   :   22 (   0 singleton) *)

(*             Maximal term depth    :    5 (   3 average) *)

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

(* -------------------------------------------------------------------------- *)
ntheorem prove_wajsberg_ntheorem:
 (∀Univ:Type.∀X:Univ.∀Y:Univ.∀Z:Univ.
∀myand:∀_:Univ.∀_:Univ.Univ.
∀implies:∀_:Univ.∀_:Univ.Univ.
∀not:∀_:Univ.Univ.
∀or:∀_:Univ.∀_:Univ.Univ.
∀truth:Univ.
∀x:Univ.
∀H0:∀X:Univ.∀Y:Univ.eq Univ (myand X Y) (myand Y X).
∀H1:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (myand (myand X Y) Z) (myand X (myand Y Z)).
∀H2:∀X:Univ.∀Y:Univ.eq Univ (myand X Y) (not (or (not X) (not Y))).
∀H3:∀X:Univ.∀Y:Univ.eq Univ (or X Y) (or Y X).
∀H4:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (or (or X Y) Z) (or X (or Y Z)).
∀H5:∀X:Univ.∀Y:Univ.eq Univ (or X Y) (implies (not X) Y).
∀H6:∀X:Univ.∀Y:Univ.eq Univ (implies (implies (not X) (not Y)) (implies Y X)) truth.
∀H7:∀X:Univ.∀Y:Univ.eq Univ (implies (implies X Y) Y) (implies (implies Y X) X).
∀H8:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (implies (implies X Y) (implies (implies Y Z) (implies X Z))) truth.
∀H9:∀X:Univ.eq Univ (implies truth X) X.eq Univ (not (or (myand x (or x x)) (myand x x))) (myand (not x) (or (or (not x) (not x)) (myand (not x) (not x)))))
.
#Univ ##.
#X ##.
#Y ##.
#Z ##.
#myand ##.
#implies ##.
#not ##.
#or ##.
#truth ##.
#x ##.
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
nauto by H0,H1,H2,H3,H4,H5,H6,H7,H8,H9 ##;
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)

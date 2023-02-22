include "logic/equality.ma".

(* Inclusion of: LCL109-6.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : LCL109-6 : TPTP v3.7.0. Released v1.0.0. *)

(*  Domain   : Logic Calculi (Wajsberg Algebra) *)

(*  Problem  : A ntheorem in the lattice structure of Wajsberg algebras *)

(*  Version  : [Bon91] (equality) axioms : Augmented. *)

(*             Theorem formulation : Alternative Wajsberg algebras lattice  *)

(*             structure. *)

(*  English  :  *)

(*  Refs     : [FRT84] Font et al. (1984), Wajsberg Algebras *)

(*           : [AB90]  Anantharaman & Bonacina (1990), An Application of the  *)

(*           : [Bon91] Bonacina (1991), Problems in Lukasiewicz Logic *)

(*  Source   : [Bon91] *)

(*  Names    : Lattice structure ntheorem 8 [Bon91] *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.11 v3.4.0, 0.12 v3.3.0, 0.14 v3.1.0, 0.11 v2.7.0, 0.09 v2.6.0, 0.17 v2.5.0, 0.00 v2.4.0, 0.00 v2.2.1, 0.67 v2.2.0, 0.71 v2.1.0, 0.88 v2.0.0 *)

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

(*  File     : LCL002-0 : TPTP v3.7.0. Released v1.0.0. *)

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

(*             Number of atoms      :    8 (   8 equality) *)

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
ntheorem prove_wajsberg_mv_4:
 (∀Univ:Type.∀X:Univ.∀Y:Univ.∀Z:Univ.
∀a:Univ.
∀and_star:∀_:Univ.∀_:Univ.Univ.
∀b:Univ.
∀falsehood:Univ.
∀implies:∀_:Univ.∀_:Univ.Univ.
∀not:∀_:Univ.Univ.
∀truth:Univ.
∀xor:∀_:Univ.∀_:Univ.Univ.
∀H0:∀X:Univ.∀Y:Univ.eq Univ (implies X Y) (xor truth (and_star X (xor truth Y))).
∀H1:eq Univ (not truth) falsehood.
∀H2:∀X:Univ.∀Y:Univ.eq Univ (and_star X Y) (and_star Y X).
∀H3:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (and_star (and_star X Y) Z) (and_star X (and_star Y Z)).
∀H4:∀X:Univ.∀Y:Univ.eq Univ (xor X Y) (xor Y X).
∀H5:∀X:Univ.∀Y:Univ.eq Univ (and_star (xor (and_star (xor truth X) Y) truth) Y) (and_star (xor (and_star (xor truth Y) X) truth) X).
∀H6:∀X:Univ.∀Y:Univ.eq Univ (xor X (xor truth Y)) (xor (xor X truth) Y).
∀H7:∀X:Univ.eq Univ (and_star (xor truth X) X) falsehood.
∀H8:∀X:Univ.eq Univ (and_star X falsehood) falsehood.
∀H9:∀X:Univ.eq Univ (and_star X truth) X.
∀H10:∀X:Univ.eq Univ (xor X X) falsehood.
∀H11:∀X:Univ.eq Univ (xor X falsehood) X.
∀H12:∀X:Univ.eq Univ (not X) (xor X truth).eq Univ (implies (implies (implies a b) (implies b a)) (implies b a)) truth)
.
#Univ ##.
#X ##.
#Y ##.
#Z ##.
#a ##.
#and_star ##.
#b ##.
#falsehood ##.
#implies ##.
#not ##.
#truth ##.
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
nauto by H0,H1,H2,H3,H4,H5,H6,H7,H8,H9,H10,H11,H12 ##;
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)

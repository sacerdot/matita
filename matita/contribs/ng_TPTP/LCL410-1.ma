include "logic/equality.ma".

(* Inclusion of: LCL410-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : LCL410-1 : TPTP v3.7.0. Released v2.5.0. *)

(*  Domain   : Logic Calculi (Wajsberg Algebras) *)

(*  Problem  : Alternative Wajsberg algebra definitions *)

(*  Version  : [AB90] (equality) axioms. *)

(*  English  :  *)

(*  Refs     : [FRT84] Font et al. (1984), Wajsberg Algebras *)

(*           : [AB90]  Anantharaman & Bonacina (1990), An Application of the  *)

(*           : [Bon91] Bonacina (1991), Problems in Lukasiewicz Logic *)

(*  Source   : [Bon91] *)

(*  Names    :  *)

(*  Status   : Satisfiable *)

(*  Rating   : 0.00 v3.2.0, 0.33 v3.1.0, 0.00 v2.5.0 *)

(*  Syntax   : Number of clauses     :   20 (   0 non-Horn;  20 unit;   1 RR) *)

(*             Number of atoms       :   20 (  20 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    8 (   2 constant; 0-2 arity) *)

(*             Number of variables   :   35 (   1 singleton) *)

(*             Maximal term depth    :    5 (   2 average) *)

(*  Comments :  *)

(* -------------------------------------------------------------------------- *)

(* ----Include Alternative Wajsberg algebra axioms *)

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

(* ----Include Wajsberg algebra AND and OR definitions *)

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

(* ----Include Alternative Wajsberg algebra definitions *)

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

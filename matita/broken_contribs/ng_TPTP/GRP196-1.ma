include "logic/equality.ma".

(* Inclusion of: GRP196-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : GRP196-1 : TPTP v3.7.0. Released v2.2.0. *)

(*  Domain   : Group Theory (Semigroups) *)

(*  Problem  : In semigroups, xyyy=yyyx -> (uy)^9 = u^9v^9. *)

(*  Version  : [MP96] (equality) axioms. *)

(*  English  :  *)

(*  Refs     : [McC98] McCune (1998), Email to G. Sutcliffe *)

(*           : [MP96]  McCune & Padmanabhan (1996), Automated Deduction in Eq *)

(*           : [McC95] McCune (1995), Four Challenge Problems in Equational L *)

(*  Source   : [McC98] *)

(*  Names    : CS-3 [MP96] *)

(*           : Problem B [McC95] *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.89 v3.4.0, 1.00 v3.3.0, 0.93 v3.1.0, 1.00 v2.2.1 *)

(*  Syntax   : Number of clauses     :    3 (   0 non-Horn;   3 unit;   1 RR) *)

(*             Number of atoms       :    3 (   3 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    3 (   2 constant; 0-2 arity) *)

(*             Number of variables   :    5 (   0 singleton) *)

(*             Maximal term depth    :   18 (   8 average) *)

(*  Comments : The problem was originally posed for cancellative semigroups, *)

(*             Otter does this with a nonstandard representation [MP96]. *)

(* -------------------------------------------------------------------------- *)

(* ----Include semigroups axioms *)

(* Inclusion of: Axioms/GRP008-0.ax *)

(* -------------------------------------------------------------------------- *)

(*  File     : GRP008-0 : TPTP v3.7.0. Released v2.2.0. *)

(*  Domain   : Group Theory (Semigroups) *)

(*  Axioms   : Semigroups axioms *)

(*  Version  : [MP96] (equality) axioms. *)

(*  English  :  *)

(*  Refs     : [McC98] McCune (1998), Email to G. Sutcliffe *)

(*           : [MP96]  McCune & Padmanabhan (1996), Automated Deduction in Eq *)

(*  Source   : [McC98] *)

(*  Names    :  *)

(*  Status   :  *)

(*  Syntax   : Number of clauses    :    1 (   0 non-Horn;   1 unit;   0 RR) *)

(*             Number of atoms      :    1 (   1 equality) *)

(*             Maximal clause size  :    1 (   1 average) *)

(*             Number of predicates :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors   :    1 (   0 constant; 2-2 arity) *)

(*             Number of variables  :    3 (   0 singleton) *)

(*             Maximal term depth   :    3 (   3 average) *)

(*  Comments :  *)

(* -------------------------------------------------------------------------- *)

(* ----Associativity: *)

(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)

(* ----Hypothesis: *)

(* ----Denial of conclusion: *)
ntheorem prove_this:
 (∀Univ:Type.∀X:Univ.∀Y:Univ.∀Z:Univ.
∀a:Univ.
∀b:Univ.
∀multiply:∀_:Univ.∀_:Univ.Univ.
∀H0:∀X:Univ.∀Y:Univ.eq Univ (multiply X (multiply Y (multiply Y Y))) (multiply Y (multiply Y (multiply Y X))).
∀H1:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (multiply (multiply X Y) Z) (multiply X (multiply Y Z)).eq Univ (multiply a (multiply b (multiply a (multiply b (multiply a (multiply b (multiply a (multiply b (multiply a (multiply b (multiply a (multiply b (multiply a (multiply b (multiply a (multiply b (multiply a b))))))))))))))))) (multiply a (multiply a (multiply a (multiply a (multiply a (multiply a (multiply a (multiply a (multiply a (multiply b (multiply b (multiply b (multiply b (multiply b (multiply b (multiply b (multiply b b))))))))))))))))))
.
#Univ ##.
#X ##.
#Y ##.
#Z ##.
#a ##.
#b ##.
#multiply ##.
#H0 ##.
#H1 ##.
nauto by H0,H1 ##;
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)

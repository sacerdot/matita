(**************************************************************************)
(*       ___                                                              *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||         The HELM team.                                      *)
(*      ||A||         http://helm.cs.unibo.it                             *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU General Public License Version 2                  *)
(*                                                                        *)
(**************************************************************************)

(* This file was automatically generated: do not edit *********************)

include "preamble.ma".

(* From Arith/Compare *****************************************************)

(* NOTATION
Notation not_eq_sym := sym_not_eq.
*)

(* From Bool/Bool *********************************************************)

(* NOTATION
Infix "||" := orb (at level 50, left associativity) : bool_scope.
*)

(* NOTATION
Infix "&&" := andb (at level 40, left associativity) : bool_scope.
*)

(* From Init/Datatypes ****************************************************)

(* NOTATION
Add Printing If bool.
*)

(* NOTATION
Notation "x + y" := (sum x y) : type_scope.
*)

(* NOTATION
Add Printing Let prod.
*)

(* NOTATION
Notation "x * y" := (prod x y) : type_scope.
*)

(* NOTATION
Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) : core_scope.
*)

(* From Init/Logic ********************************************************)

(* NOTATION
Notation "~ x" := (not x) : type_scope.
*)

(* NOTATION
Notation "A <-> B" := (iff A B) : type_scope.
*)

(* NOTATION
Notation "'IF' c1 'then' c2 'else' c3" := (IF_then_else c1 c2 c3)
  (at level 200) : type_scope.
*)

(* NOTATION
Notation "'exists' x , p" := (ex (fun x => p))
  (at level 200, x ident) : type_scope.
*)

(* NOTATION
Notation "'exists' x : t , p" := (ex (fun x:t => p))
  (at level 200, x ident, format "'exists'  '/  ' x  :  t ,  '/  ' p")
  : type_scope.
*)

(* NOTATION
Notation "'exists2' x , p & q" := (ex2 (fun x => p) (fun x => q))
  (at level 200, x ident, p at level 200) : type_scope.
*)

(* NOTATION
Notation "'exists2' x : t , p & q" := (ex2 (fun x:t => p) (fun x:t => q))
  (at level 200, x ident, t at level 200, p at level 200,
   format "'exists2'  '/  ' x  :  t ,  '/  ' '[' p  &  '/' q ']'")
  : type_scope.
*)

(* NOTATION
Notation "x = y" := (x = y :>_) : type_scope.
*)

(* NOTATION
Notation "x <> y  :> T" := (~ x = y :>T) : type_scope.
*)

(* NOTATION
Notation "x <> y" := (x <> y :>_) : type_scope.
*)

(* From Init/Notations ****************************************************)

(* NOTATION
Reserved Notation "x <-> y" (at level 95, no associativity).
*)

(* NOTATION
Reserved Notation "x /\ y" (at level 80, right associativity).
*)

(* NOTATION
Reserved Notation "x \/ y" (at level 85, right associativity).
*)

(* NOTATION
Reserved Notation "~ x" (at level 75, right associativity).
*)

(* NOTATION
Reserved Notation "x = y  :> T"
(at level 70, y at next level, no associativity).
*)

(* NOTATION
Reserved Notation "x = y" (at level 70, no associativity).
*)

(* NOTATION
Reserved Notation "x = y = z"
(at level 70, no associativity, y at next level).
*)

(* NOTATION
Reserved Notation "x <> y  :> T"
(at level 70, y at next level, no associativity).
*)

(* NOTATION
Reserved Notation "x <> y" (at level 70, no associativity).
*)

(* NOTATION
Reserved Notation "x <= y" (at level 70, no associativity).
*)

(* NOTATION
Reserved Notation "x < y" (at level 70, no associativity).
*)

(* NOTATION
Reserved Notation "x >= y" (at level 70, no associativity).
*)

(* NOTATION
Reserved Notation "x > y" (at level 70, no associativity).
*)

(* NOTATION
Reserved Notation "x <= y <= z" (at level 70, y at next level).
*)

(* NOTATION
Reserved Notation "x <= y < z" (at level 70, y at next level).
*)

(* NOTATION
Reserved Notation "x < y < z" (at level 70, y at next level).
*)

(* NOTATION
Reserved Notation "x < y <= z" (at level 70, y at next level).
*)

(* NOTATION
Reserved Notation "x + y" (at level 50, left associativity).
*)

(* NOTATION
Reserved Notation "x - y" (at level 50, left associativity).
*)

(* NOTATION
Reserved Notation "x * y" (at level 40, left associativity).
*)

(* NOTATION
Reserved Notation "x / y" (at level 40, left associativity).
*)

(* NOTATION
Reserved Notation "- x" (at level 35, right associativity).
*)

(* NOTATION
Reserved Notation "/ x" (at level 35, right associativity).
*)

(* NOTATION
Reserved Notation "x ^ y" (at level 30, right associativity).
*)

(* NOTATION
Reserved Notation "( x , y , .. , z )" (at level 0).
*)

(* NOTATION
Reserved Notation "{ x }" (at level 0, x at level 99).
*)

(* NOTATION
Reserved Notation "{ A } + { B }" (at level 50, left associativity).
*)

(* NOTATION
Reserved Notation "A + { B }" (at level 50, left associativity).
*)

(* NOTATION
Reserved Notation "{ x : A  |  P }" (at level 0, x at level 99).
*)

(* NOTATION
Reserved Notation "{ x : A  |  P  &  Q }" (at level 0, x at level 99).
*)

(* NOTATION
Reserved Notation "{ x : A  &  P }" (at level 0, x at level 99).
*)

(* NOTATION
Reserved Notation "{ x : A  &  P  &  Q }" (at level 0, x at level 99).
*)

(* From Init/Peano ********************************************************)

(* NOTATION
Infix "+" := plus : nat_scope.
*)

(* NOTATION
Infix "*" := mult : nat_scope.
*)

(* NOTATION
Infix "-" := minus : nat_scope.
*)

(* NOTATION
Infix "<=" := le : nat_scope.
*)

(* NOTATION
Infix "<" := lt : nat_scope.
*)

(* NOTATION
Infix ">=" := ge : nat_scope.
*)

(* NOTATION
Infix ">" := gt : nat_scope.
*)

(* NOTATION
Notation "x <= y <= z" := (x <= y /\ y <= z) : nat_scope.
*)

(* NOTATION
Notation "x <= y < z" := (x <= y /\ y < z) : nat_scope.
*)

(* NOTATION
Notation "x < y < z" := (x < y /\ y < z) : nat_scope.
*)

(* NOTATION
Notation "x < y <= z" := (x < y /\ y <= z) : nat_scope.
*)

(* From Init/Specif *******************************************************)

(* NOTATION
Notation "{ x : A  |  P }" := (sig (fun x:A => P)) : type_scope.
*)

(* NOTATION
Notation "{ x : A  |  P  &  Q }" := (sig2 (fun x:A => P) (fun x:A => Q)) :
  type_scope.
*)

(* NOTATION
Notation "{ x : A  &  P }" := (sigS (fun x:A => P)) : type_scope.
*)

(* NOTATION
Notation "{ x : A  &  P  &  Q }" := (sigS2 (fun x:A => P) (fun x:A => Q)) :
  type_scope.
*)

(* NOTATION
Add Printing Let sig.
*)

(* NOTATION
Add Printing Let sig2.
*)

(* NOTATION
Add Printing Let sigS.
*)

(* NOTATION
Add Printing Let sigS2.
*)

(* NOTATION
Add Printing If sumbool.
*)

(* NOTATION
Add Printing If sumor.
*)

(* From Lists/List ********************************************************)

(* NOTATION
Infix "::" := cons (at level 60, right associativity) : list_scope.
*)

(* NOTATION
Infix "++" := app (right associativity, at level 60) : list_scope.
*)

(* NOTATION
Infix "::" := cons (at level 60, right associativity) : list_scope.
*)

(* NOTATION
Infix "++" := app (right associativity, at level 60) : list_scope.
*)

(* From NArith/BinNat *****************************************************)

(* NOTATION
Infix "+" := Nplus : N_scope.
*)

(* NOTATION
Infix "*" := Nmult : N_scope.
*)

(* NOTATION
Infix "?=" := Ncompare (at level 70, no associativity) : N_scope.
*)

(* From NArith/BinPos *****************************************************)

(* NOTATION
Infix "+" := Pplus : positive_scope.
*)

(* NOTATION
Infix "-" := Pminus : positive_scope.
*)

(* NOTATION
Infix "*" := Pmult : positive_scope.
*)

(* NOTATION
Infix "/" := Pdiv2 : positive_scope.
*)

(* NOTATION
Infix "?=" := Pcompare (at level 70, no associativity) : positive_scope.
*)

(* From Reals/RIneq *******************************************************)

(* NOTATION
Add Field R Rplus Rmult 1 0 Ropp (fun x y:R => false) Rinv RTheory Rinv_l
 with minus := Rminus div := Rdiv.
*)

(* From Reals/Ranalysis1 **************************************************)

(* NOTATION
Infix "+" := plus_fct : Rfun_scope.
*)

(* NOTATION
Notation "- x" := (opp_fct x) : Rfun_scope.
*)

(* NOTATION
Infix "*" := mult_fct : Rfun_scope.
*)

(* NOTATION
Infix "-" := minus_fct : Rfun_scope.
*)

(* NOTATION
Infix "/" := div_fct : Rfun_scope.
*)

(* NOTATION
Notation Local "f1 'o' f2" := (comp f1 f2)
  (at level 20, right associativity) : Rfun_scope.
*)

(* NOTATION
Notation "/ x" := (inv_fct x) : Rfun_scope.
*)

(* From Reals/Rdefinitions ************************************************)

(* NOTATION
Infix "+" := Rplus : R_scope.
*)

(* NOTATION
Infix "*" := Rmult : R_scope.
*)

(* NOTATION
Notation "- x" := (Ropp x) : R_scope.
*)

(* NOTATION
Notation "/ x" := (Rinv x) : R_scope.
*)

(* NOTATION
Infix "<" := Rlt : R_scope.
*)

(* NOTATION
Infix "-" := Rminus : R_scope.
*)

(* NOTATION
Infix "/" := Rdiv : R_scope.
*)

(* NOTATION
Infix "<=" := Rle : R_scope.
*)

(* NOTATION
Infix ">=" := Rge : R_scope.
*)

(* NOTATION
Infix ">" := Rgt : R_scope.
*)

(* NOTATION
Notation "x <= y <= z" := ((x <= y)%R /\ (y <= z)%R) : R_scope.
*)

(* NOTATION
Notation "x <= y < z" := ((x <= y)%R /\ (y < z)%R) : R_scope.
*)

(* NOTATION
Notation "x < y < z" := ((x < y)%R /\ (y < z)%R) : R_scope.
*)

(* NOTATION
Notation "x < y <= z" := ((x < y)%R /\ (y <= z)%R) : R_scope.
*)

(* From Reals/Rfunctions **************************************************)

(* NOTATION
Infix "^" := pow : R_scope.
*)

(* NOTATION
Infix Local "^Z" := powerRZ (at level 30, right associativity) : R_scope.
*)

(* From Reals/Rpower ******************************************************)

(* NOTATION
Infix Local "^R" := Rpower (at level 30, right associativity) : R_scope.
*)

(* From Reals/Rtopology ***************************************************)

(* NOTATION
Infix "=_D" := eq_Dom (at level 70, no associativity).
*)

(* From Setoids/Setoid ****************************************************)

(* NOTATION
Add Setoid Prop iff Prop_S.
*)

(* From Wellfounded/Disjoint_Union ****************************************)

(* NOTATION
Notation Le_AsB := (le_AsB A B leA leB).
*)

(* From Wellfounded/Lexicographic_Exponentiation **************************)

(* NOTATION
Notation Power := (Pow A leA).
*)

(* NOTATION
Notation Lex_Exp := (lex_exp A leA).
*)

(* NOTATION
Notation ltl := (Ltl A leA).
*)

(* NOTATION
Notation Descl := (Desc A leA).
*)

(* NOTATION
Notation List := (list A).
*)

(* NOTATION
Notation Nil := (nil (A:=A)).
*)

(* NOTATION
Notation Cons := (cons (A:=A)).
*)

(* NOTATION
Notation "<< x , y >>" := (exist Descl x y) (at level 0, x, y at level 100).
*)

(* From Wellfounded/Lexicographic_Product *********************************)

(* NOTATION
Notation LexProd := (lexprod A B leA leB).
*)

(* NOTATION
Notation Symprod := (symprod A B leA leB).
*)

(* NOTATION
Notation SwapProd := (swapprod A R).
*)

(* From Wellfounded/Transitive_Closure ************************************)

(* NOTATION
Notation trans_clos := (clos_trans A R).
*)

(* From Wellfounded/Union *************************************************)

(* NOTATION
Notation Union := (union A R1 R2).
*)

(* From ZArith/BinInt *****************************************************)

(* NOTATION
Infix "+" := Zplus : Z_scope.
*)

(* NOTATION
Notation "- x" := (Zopp x) : Z_scope.
*)

(* NOTATION
Infix "-" := Zminus : Z_scope.
*)

(* NOTATION
Infix "*" := Zmult : Z_scope.
*)

(* NOTATION
Infix "?=" := Zcompare (at level 70, no associativity) : Z_scope.
*)

(* NOTATION
Infix "<=" := Zle : Z_scope.
*)

(* NOTATION
Infix "<" := Zlt : Z_scope.
*)

(* NOTATION
Infix ">=" := Zge : Z_scope.
*)

(* NOTATION
Infix ">" := Zgt : Z_scope.
*)

(* NOTATION
Notation "x <= y <= z" := (x <= y /\ y <= z) : Z_scope.
*)

(* NOTATION
Notation "x <= y < z" := (x <= y /\ y < z) : Z_scope.
*)

(* NOTATION
Notation "x < y < z" := (x < y /\ y < z) : Z_scope.
*)

(* NOTATION
Notation "x < y <= z" := (x < y /\ y <= z) : Z_scope.
*)

(* From ZArith/Zdiv *******************************************************)

(* NOTATION
Infix "/" := Zdiv : Z_scope.
*)

(* NOTATION
Infix "mod" := Zmod (at level 40, no associativity) : Z_scope.
*)

(* From ZArith/Znumtheory *************************************************)

(* NOTATION
Notation "( a | b )" := (Zdivide a b) (at level 0) : Z_scope.
*)

(* From ZArith/Zpower *****************************************************)

(* NOTATION
Infix "^" := Zpower : Z_scope.
*)

(* NOTATION
Infix "^" := Zpower : Z_scope.
*)


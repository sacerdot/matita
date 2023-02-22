(**************************************************************************)
(*       ___	                                                            *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||       A.Asperti, C.Sacerdoti Coen,                          *)
(*      ||A||       E.Tassi, S.Zacchiroli                                 *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU Lesser General Public License Version 2.1         *)
(*                                                                        *)
(**************************************************************************)

include "arithmetics/nat.ma".

ninductive Z : Type ≝
  OZ : Z
| pos : nat → Z
| neg : nat → Z.

interpretation "Integers" 'Z = Z.

ndefinition Z_of_nat ≝
λn. match n with
[ O ⇒ OZ 
| S n ⇒ pos n].

ncoercion Z_of_nat : ∀n:nat.Z ≝ Z_of_nat on _n:nat to Z.

ndefinition neg_Z_of_nat \def
λn. match n with
[ O ⇒ OZ 
| S n ⇒ neg n].

nlemma pos_n_eq_S_n : ∀n : nat.pos n = S n.
//.
nqed.

ndefinition abs ≝
λz.match z with 
[ OZ ⇒ O
| pos n ⇒ S n
| neg n ⇒ S n].

ndefinition OZ_test ≝
λz.match z with 
[ OZ ⇒ true
| pos _ ⇒ false
| neg _ ⇒ false].

ntheorem OZ_test_to_Prop : ∀z:Z.
  match OZ_test z with
  [true ⇒ z=OZ 
  |false ⇒ z ≠ OZ].
#z;ncases z
##[napply refl
##|##*:#z1;napply nmk;#H;ndestruct]
nqed.

(* discrimination *)
ntheorem injective_pos: injective nat Z pos.
#n;#m;#H;ndestruct;//;
nqed.

(* variant inj_pos : \forall n,m:nat. pos n = pos m \to n = m
\def injective_pos. *)

ntheorem injective_neg: injective nat Z neg.
#n;#m;#H;ndestruct;//;
nqed.

(* variant inj_neg : \forall n,m:nat. neg n = neg m \to n = m
\def injective_neg. *)

ntheorem not_eq_OZ_pos: ∀n:nat. OZ ≠ pos n.
#n;napply nmk;#H;ndestruct;
nqed.

ntheorem not_eq_OZ_neg :∀n:nat. OZ ≠ neg n.
#n;napply nmk;#H;ndestruct;
nqed.

ntheorem not_eq_pos_neg : ∀n,m:nat. pos n ≠ neg m.
#n;#m;napply nmk;#H;ndestruct;
nqed.

ntheorem decidable_eq_Z : ∀x,y:Z. decidable (x=y).
#x;#y;ncases x;
##[ncases y;
   ##[@;//
   ##|##*:#n;@2;napply nmk;#H;ndestruct]
##|#n;ncases y;
   ##[@2;napply nmk;#H;ndestruct;
   ##|#m;ncases (decidable_eq_nat n m);#H;
      ##[nrewrite > H;@;//
      ##|@2;napply nmk;#H2;nelim H;
         (* bug if you don't introduce H3 *)#H3;ndestruct;
         napply H3;@]
   ##|#m;@2;napply nmk;#H;ndestruct]
##|#n;ncases y;
   ##[@2;napply nmk;#H;ndestruct;
   ##|#m;@2;napply nmk;#H;ndestruct
   ##|#m;ncases (decidable_eq_nat n m);#H;
      ##[nrewrite > H;@;//
      ##|@2;napply nmk;#H2;nelim H;#H3;ndestruct;
         napply H3;@]##]##]
nqed.

ndefinition Zsucc ≝
λz. match z with
[ OZ ⇒ pos O
| pos n ⇒ pos (S n)
| neg n ⇒
	  match n with
	  [ O ⇒ OZ
	  | S p ⇒ neg p]].

ndefinition Zpred ≝
λz. match z with
[ OZ ⇒ neg O
| pos n ⇒
	  match n with
	  [ O ⇒ OZ
	  | S p ⇒ pos p]
| neg n ⇒ neg (S n)].

ntheorem Zpred_Zsucc: ∀z:Z. Zpred (Zsucc z) = z.
#z;ncases z;
##[##1,2://
##|#n;ncases n;//]
nqed.

ntheorem Zsucc_Zpred: ∀z:Z. Zsucc (Zpred z) = z.
#z;ncases z
##[##2:#n;ncases n;//
##|##*://]
nqed.

ndefinition Zle : Z → Z → Prop ≝
λx,y:Z.
  match x with
  [ OZ ⇒ 
    match y with 
    [ OZ ⇒ True
    | pos m ⇒ True
    | neg m ⇒ False ]
  | pos n ⇒
    match y with 
    [ OZ ⇒ False
    | pos m ⇒ n ≤ m
    | neg m ⇒ False ]
  | neg n ⇒
    match y with 
    [ OZ ⇒ True
    | pos m ⇒ True
    | neg m ⇒ m ≤ n ]].

interpretation "integer 'less or equal to'" 'leq x y = (Zle x y).
interpretation "integer 'neither less nor equal to'" 'nleq x y = (Not (Zle x y)).

ndefinition Zlt : Z → Z → Prop ≝
λx,y:Z.
  match x with
  [ OZ ⇒
    match y with 
    [ OZ ⇒ False
    | pos m ⇒ True
    | neg m ⇒ False ]
  | pos n ⇒
    match y with 
    [ OZ ⇒ False
    | pos m ⇒ n<m
    | neg m ⇒ False ]
  | neg n ⇒
    match y with 
    [ OZ ⇒ True
    | pos m ⇒ True
    | neg m ⇒ m<n ]].
    
interpretation "integer 'less than'" 'lt x y = (Zlt x y).
interpretation "integer 'not less than'" 'nless x y = (Not (Zlt x y)).

ntheorem irreflexive_Zlt: irreflexive Z Zlt.
#x;ncases x
##[napply nmk;//
##|##*:#n;napply (not_le_Sn_n n) (* XXX: auto?? *)]
nqed.

(* transitivity *)
ntheorem transitive_Zle : transitive Z Zle.
#x;#y;#z;ncases x
##[ncases y
   ##[//
   ##|##*:#n;ncases z;//]
##|#n;ncases y
   ##[#H;ncases H
   ##|(*##*:#m;#Hl;ncases z;//;*)
      #m;#Hl;ncases z;//;#p;#Hr;
      napply (transitive_le n m p);//; (* XXX: auto??? *)
   ##|#m;#Hl;ncases Hl]
##|#n;ncases y
   ##[#Hl;ncases z
      ##[##1,2://
      ##|#m;#Hr;ncases Hr]
   ##|#m;#Hl;ncases z;
      ##[##1,2://
      ##|#p;#Hr;ncases Hr]
   ##|#m;#Hl;ncases z;//;#p;#Hr;
      napply (transitive_le p m n);//; (* XXX: auto??? *) ##]
nqed.

(* variant trans_Zle: transitive Z Zle
\def transitive_Zle.*)

ntheorem transitive_Zlt: transitive Z Zlt.
#x;#y;#z;ncases x
##[ncases y
   ##[//
   ##|#n;ncases z
      ##[#_;#Hr;ncases Hr
      ##|//
      ##|#m;#_;#Hr;ncases Hr]
   ##|#n;#Hl;ncases Hl]
##|#n;ncases y
   ##[#Hl;ncases Hl
   ##|#m;ncases z
      ##[//
      ##|#p;napply transitive_lt (* XXX: auto??? *) 
      ##|//##]
   ##|#m;#Hl;ncases Hl]
##|#n;ncases y
   ##[ncases z;
      ##[##1,2://
      ##|#m;#_;#Hr;ncases Hr]
   ##|#m;ncases z;
      ##[##1,2://
      ##|#p;#_;#Hr;ncases Hr]
   ##|#m;ncases z
      ##[##1,2://
      ##|#p;#Hl;#Hr;napply (transitive_lt … Hr Hl)]
   ##]
##]
nqed.     

(* variant trans_Zlt: transitive Z Zlt
\def transitive_Zlt.
theorem irrefl_Zlt: irreflexive Z Zlt
\def irreflexive_Zlt.*)

ntheorem Zlt_neg_neg_to_lt: 
  ∀n,m:nat. neg n < neg m → m < n.
//;
nqed.

ntheorem lt_to_Zlt_neg_neg: ∀n,m:nat.m < n → neg n < neg m. 
//;
nqed.

ntheorem Zlt_pos_pos_to_lt: 
  ∀n,m:nat. pos n < pos m → n < m.
//;
nqed.

ntheorem lt_to_Zlt_pos_pos: ∀n,m:nat.n < m → pos n < pos m. 
//;
nqed.

ntheorem Zlt_to_Zle: ∀x,y:Z. x < y → Zsucc x ≤ y.
#x;#y;ncases x
##[ncases y
   ##[#H;ncases H
   ##|//;
   ##|#p;#H;ncases H]
##|#n;ncases y
   ##[#H;ncases H
   ##|#p;nnormalize;//
   ##|#p;#H;ncases H]
##|#n;ncases y
   ##[##1,2:ncases n;//
   ##|#p;ncases n;nnormalize;
      ##[#H;nelim (not_le_Sn_O p);#H2;napply H2;//; (* XXX: auto? *)
      ##|#m;napply le_S_S_to_le (* XXX: auto? *)]
   ##]
##]
nqed.

(*** COMPARE ***)

(* boolean equality *)
ndefinition eqZb : Z → Z → bool ≝
λx,y:Z.
  match x with
  [ OZ ⇒
      match y with
        [ OZ ⇒ true
        | pos q ⇒ false
        | neg q ⇒ false]
  | pos p ⇒
      match y with
        [ OZ ⇒ false
        | pos q ⇒ eqb p q
        | neg q ⇒ false]     
  | neg p ⇒
      match y with
        [ OZ ⇒ false
        | pos q ⇒ false
        | neg q ⇒ eqb p q]].

ntheorem eqZb_to_Prop: 
  ∀x,y:Z. 
    match eqZb x y with
    [ true ⇒ x=y
    | false ⇒ x ≠ y].
#x;#y;ncases x
##[ncases y;
   ##[//
   ##|napply not_eq_OZ_pos (* XXX: auto? *)
   ##|napply not_eq_OZ_neg (* XXX: auto? *)]
##|#n;ncases y;
   ##[napply nmk;#H;nelim (not_eq_OZ_pos n);#H2;/2/;
   ##|#m;napply eqb_elim;
      ##[//
      ##|#H;napply nmk;#H2;nelim H;#H3;ndestruct;/2/]
   ##|#m;napply not_eq_pos_neg]
##|#n;ncases y
   ##[napply nmk;#H;nelim (not_eq_OZ_neg n);#H;/2/;
   ##|#m;napply nmk;#H;ndestruct
   ##|#m;napply eqb_elim;
      ##[//
      ##|#H;napply nmk;#H2;ndestruct;nelim H;/2/]
   ##]
##]
nqed.

ntheorem eqZb_elim: ∀x,y:Z.∀P:bool → Prop.
  (x=y → P true) → (x ≠ y → P false) → P (eqZb x y).
#x;#y;#P;#HP1;#HP2;
ncut 
(match (eqZb x y) with
[ true ⇒ x=y
| false ⇒ x ≠ y] → P (eqZb x y))
##[ncases (eqZb x y);nnormalize; (* XXX: auto?? *)
   ##[napply HP1
   ##|napply HP2]
##|#Hcut;napply Hcut;napply eqZb_to_Prop]
nqed.

ndefinition Z_compare : Z → Z → compare ≝
λx,y:Z.
  match x with
  [ OZ ⇒
    match y with 
    [ OZ ⇒ EQ
    | pos m ⇒ LT
    | neg m ⇒ GT ]
  | pos n ⇒
    match y with 
    [ OZ ⇒ GT
    | pos m ⇒ nat_compare n m
    | neg m ⇒ GT]
  | neg n ⇒ 
    match y with 
    [ OZ ⇒ LT
    | pos m ⇒ LT
    | neg m ⇒ nat_compare m n ]].

ntheorem Z_compare_to_Prop : 
∀x,y:Z. match (Z_compare x y) with
[ LT ⇒ x < y
| EQ ⇒ x=y
| GT ⇒ y < x]. 
#x;#y;nelim x
##[nelim y;//;
##|nelim y
   ##[##1,3://
   ##|#n;#m;nnormalize;
      ncut (match (nat_compare m n) with
      [ LT ⇒ m < n
      | EQ ⇒ m = n
      | GT ⇒ n < m ] →
      match (nat_compare m n) with
      [ LT ⇒ S m  ≤ n
      | EQ ⇒ pos m = pos n
      | GT ⇒ S n  ≤ m])
      ##[ncases (nat_compare m n);//
      ##|#Hcut;napply Hcut;napply nat_compare_to_Prop]
   ##]
##|nelim y
   ##[#n;//
   ##|nnormalize;//
   ##|nnormalize;#n;#m;
      ncut (match (nat_compare n m) with
        [ LT ⇒ n < m
        | EQ ⇒ n = m
        | GT ⇒ m < n] →
      match (nat_compare n m) with
      [ LT ⇒ S n ≤ m
      | EQ ⇒ neg m = neg n
      | GT ⇒ S m ≤ n])
      ##[ncases (nat_compare n m);//
      ##|#Hcut;napply Hcut;napply nat_compare_to_Prop]
   ##]
##]
nqed.

ndefinition Zplus : Z → Z → Z ≝
  λx,y. match x with
    [ OZ ⇒ y
    | pos m ⇒
        match y with
         [ OZ ⇒ x
         | pos n ⇒ (pos (pred ((S m)+(S n))))
         | neg n ⇒ 
              match nat_compare m n with
                [ LT ⇒ (neg (pred (n-m)))
                | EQ ⇒ OZ
                | GT ⇒ (pos (pred (m-n)))] ]
    | neg m ⇒
        match y with
         [ OZ ⇒ x
         | pos n ⇒
              match nat_compare m n with
                [ LT ⇒ (pos (pred (n-m)))
                | EQ ⇒ OZ
                | GT ⇒ (neg (pred (m-n)))]     
         | neg n ⇒ (neg (pred ((S m)+(S n))))] ].

interpretation "integer plus" 'plus x y = (Zplus x y).

ntheorem eq_plus_Zplus: ∀n,m:nat. Z_of_nat (n+m) = Z_of_nat n + Z_of_nat m.
#n;#m;ncases n
##[//
##|#p;ncases m
   ##[nnormalize;//
   ##|//]
nqed.

ntheorem Zplus_z_OZ: ∀z:Z. z+OZ = z.
#z;ncases z;//;
nqed.

(* theorem symmetric_Zplus: symmetric Z Zplus. *)

ntheorem sym_Zplus : ∀x,y:Z. x+y = y+x.
#x;#y;ncases x;
##[nrewrite > (Zplus_z_OZ ?) (*XXX*);//
##|#p;ncases y
   ##[//
   ##|nnormalize;//
   ##|#q;nnormalize;nrewrite > (nat_compare_n_m_m_n ??) (*XXX*);
      ncases (nat_compare q p);//]
##|#p;ncases y
   ##[//;
   ##|#q;nnormalize;nrewrite > (nat_compare_n_m_m_n ??) (*XXX*);
      ncases (nat_compare q p);//
   ##|nnormalize;//]
##]
nqed.

ntheorem Zpred_Zplus_neg_O : ∀z. Zpred z = (neg O)+z.
#z;ncases z
##[//
##|##*:#n;ncases n;//]
nqed.

ntheorem Zsucc_Zplus_pos_O : ∀z. Zsucc z = (pos O)+z.
#z;ncases z
##[//
##|##*:#n;ncases n;//]
nqed.

ntheorem Zplus_pos_pos:
  ∀n,m. (pos n)+(pos m) = (Zsucc (pos n))+(Zpred (pos m)).
#n;#m;ncases n
##[ncases m;//
##|#p;ncases m
   ##[nnormalize;
      nrewrite < (plus_n_Sm ??);nrewrite < (plus_n_O ?); (* XXX yet again *)
      //
   ##|#q;nnormalize;nrewrite < (plus_n_Sm ??);nrewrite < (plus_n_Sm ??);//]
##]
nqed.

ntheorem Zplus_pos_neg:
  ∀n,m. (pos n)+(neg m) = (Zsucc (pos n))+(Zpred (neg m)).
//;
nqed.

ntheorem Zplus_neg_pos :
  ∀n,m. (neg n)+(pos m) = (Zsucc (neg n))+(Zpred (pos m)).
#n;#m;ncases n;ncases m;//;
nqed.

ntheorem Zplus_neg_neg:
  ∀n,m. (neg n)+(neg m) = (Zsucc (neg n))+(Zpred (neg m)).
#n;#m;ncases n
##[ncases m;//
##|#p;ncases m;nnormalize;
   ##[nrewrite > (plus_n_Sm ??);//
   ##|#q;nrewrite > (plus_n_Sm ??);//]
##]
nqed.

ntheorem Zplus_Zsucc_Zpred: ∀x,y. x+y = (Zsucc x)+(Zpred y).
#x;#y;ncases x
##[ncases y
   ##[//
   ##|#n;nrewrite < (Zsucc_Zplus_pos_O ?);nrewrite > (Zsucc_Zpred ?);//
   ##|//]
##|ncases y;//
##|ncases y
   ##[#n;nrewrite < (sym_Zplus ??);nrewrite < (sym_Zplus (Zpred OZ) ?);
      nrewrite < (Zpred_Zplus_neg_O ?);nrewrite > (Zpred_Zsucc ?);//
   ##|##*://]
nqed.

ntheorem Zplus_Zsucc_pos_pos : 
  ∀n,m. (Zsucc (pos n))+(pos m) = Zsucc ((pos n)+(pos m)).
//;
nqed.

ntheorem Zplus_Zsucc_pos_neg: 
  ∀n,m. (Zsucc (pos n))+(neg m) = (Zsucc ((pos n)+(neg m))).
#n;#m;
napply (nat_elim2 (λn,m. (Zsucc (pos n))+(neg m) = (Zsucc ((pos n)+(neg m)))))
##[#n1;nelim n1
   ##[//
   ##|#n2;#IH;nelim n2;//]
##|//
##|#n1;#m1;#IH;nrewrite < (Zplus_pos_neg ? m1);nelim IH;//]
nqed.

ntheorem Zplus_Zsucc_neg_neg : 
  ∀n,m. Zsucc (neg n) + neg m = Zsucc (neg n + neg m).
#n;#m;
napply (nat_elim2 (λ n,m. Zsucc (neg n) + neg m = Zsucc (neg n + neg m)))
##[#n1;nelim n1
   ##[//
   ##|#n2;#IH;nelim n2;//]
##|##*://]
nqed.

ntheorem Zplus_Zsucc_neg_pos: 
  ∀n,m. Zsucc (neg n)+(pos m) = Zsucc ((neg n)+(pos m)).
#n;#m;
napply (nat_elim2 (λn,m. Zsucc (neg n) + (pos m) = Zsucc (neg n + pos m)))
##[#n1;nelim n1
   ##[//
   ##|#n2;#IH;nelim n2;//]
##|//
##|#n1;#m1;#IH;nrewrite < IH;nrewrite < (Zplus_neg_pos ? (S m1));//]
nqed.

ntheorem Zplus_Zsucc : ∀x,y:Z. (Zsucc x)+y = Zsucc (x+y).
#x;#y;ncases x
##[ncases y;//;#n;nnormalize;ncases n;//;
##|##*:#n;ncases y;//]
nqed.

ntheorem Zplus_Zpred: ∀x,y:Z. (Zpred x)+y = Zpred (x+y).
#x;#y;ncut (Zpred (x+y) = Zpred ((Zsucc (Zpred x))+y))
##[nrewrite > (Zsucc_Zpred ?);//
##|#Hcut;nrewrite > Hcut;nrewrite > (Zplus_Zsucc ??);//]
nqed.

ntheorem associative_Zplus: associative Z Zplus.
(* nchange with (\forall x,y,z:Z. (x + y) + z = x + (y + z));*)
#x;#y;#z;ncases x
##[//
##|#n;nelim n
   ##[nrewrite < (Zsucc_Zplus_pos_O ?);nrewrite < (Zsucc_Zplus_pos_O ?);//;
   ##|#n1;#IH;
      nrewrite > (Zplus_Zsucc (pos n1) ?);nrewrite > (Zplus_Zsucc (pos n1) ?);
      nrewrite > (Zplus_Zsucc ((pos n1)+y) ?);//]
##|#n;nelim n
   ##[nrewrite < (Zpred_Zplus_neg_O (y+z));nrewrite < (Zpred_Zplus_neg_O y);//;
   ##|#n1;#IH;
      nrewrite > (Zplus_Zpred (neg n1) ?);nrewrite > (Zplus_Zpred (neg n1) ?);
      nrewrite > (Zplus_Zpred ((neg n1)+y) ?);//]
##]
nqed.

(* variant assoc_Zplus : \forall x,y,z:Z.  (x+y)+z = x+(y+z)
\def associative_Zplus. *)

(* Zopp *)
ndefinition Zopp : Z → Z ≝
  λx:Z. match x with
  [ OZ ⇒ OZ
  | pos n ⇒ neg n
  | neg n ⇒ pos n ].

interpretation "integer unary minus" 'uminus x = (Zopp x).

ntheorem eq_OZ_Zopp_OZ : OZ = (- OZ).
//;
nqed.

ntheorem Zopp_Zplus: ∀x,y:Z. -(x+y) = -x + -y.
#x;#y;ncases x
##[ncases y;//
##|##*:#n;ncases y;//;#m;nnormalize;napply nat_compare_elim;nnormalize;//]
nqed.

ntheorem Zopp_Zopp: ∀x:Z. --x = x.
#x;ncases x;//;
nqed.

ntheorem Zplus_Zopp: ∀ x:Z. x+ -x = OZ.
#x;ncases x
##[//
##|##*:#n;nnormalize;nrewrite > (nat_compare_n_n ?);//]
nqed.

ntheorem injective_Zplus_l: ∀x:Z.injective Z Z (λy.y+x).
#x;#z;#y;#H;
nrewrite < (Zplus_z_OZ z);nrewrite < (Zplus_z_OZ y);
nrewrite < (Zplus_Zopp x);
nrewrite < (associative_Zplus ???);nrewrite < (associative_Zplus ???);
//;
nqed.

ntheorem injective_Zplus_r: ∀x:Z.injective Z Z (λy.x+y).
#x;#z;#y;#H;
napply (injective_Zplus_l x);
nrewrite < (sym_Zplus ??);
//;
nqed.

(* minus *)
ndefinition Zminus : Z → Z → Z ≝ λx,y:Z. x + (-y).

interpretation "integer minus" 'minus x y = (Zminus x y).
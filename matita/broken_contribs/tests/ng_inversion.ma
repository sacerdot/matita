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

include "logic/pts.ma".

(*naxiom foo : ?.
##[##2:napply Prop;##|##skip]
nqed.*)

(*nlemma foo : ? → Prop.
##[#a;*)

ninductive eq (A:Type[2]) (x:A) : A → Prop ≝
| refl : eq A x x.

ninductive nat : Type[0] ≝
| O : nat
| S : nat → nat.

(*ninductive pippo : nat → Type[1] ≝
| pO  : pippo O
| pSS : ∀n.pippo n → pippo (S (S n)).
*)

ninductive list (A:Type[0]) : Type[0] ≝
| nil  : list A
| cons : A → list A → list A.

ninductive False : Prop ≝ .

naxiom daemon : False.

ninductive in_list (A:Type[0]) : A → list A → Prop ≝
| in_list_head : ∀x,l.in_list A x (cons A x l)
| in_list_cons : ∀x,y,l.in_list A x l → in_list A x (cons A y l).

ninductive ppippo : nat → Prop ≝
| ppO : ppippo O
| ppSS : ∀n.ppippo n → ppippo  (S (S n)).

ndefinition Not : Prop → Prop ≝ λP.P → False.

ninductive Typ : Type[0] ≝
| TVar : nat → Typ
| TFree : nat → Typ
| Top : Typ
| Arrow : Typ → Typ → Typ
| Forall : Typ → Typ → Typ.

ninductive bool : Type[0] ≝
| true : bool
| false : bool.

nrecord bound : Type ≝ { 
                          istype : bool;    (* is subtyping bound? *)
                          name   : nat ;    (* name *)
                          btype  : Typ      (* type to which the name is bound *)
                        }.
                        
nlet rec eqb m n ≝
 match m with
 [ O ⇒ match n with
  [ O ⇒ true
  | S q ⇒ false ]
 | S p ⇒ match n with
  [ O ⇒ false
  | S q ⇒ eqb p q ]].  
               
(*** Various kinds of substitution, not all will be used probably ***)

(* substitutes i-th dangling index in type T with type U *)
nlet rec subst_type_nat T U i ≝
    match T with
    [ TVar n ⇒ match eqb n i with
      [ true ⇒ U
      | false ⇒ T]
    | TFree X ⇒ T
    | Top ⇒ T
    | Arrow T1 T2 ⇒ Arrow (subst_type_nat T1 U i) (subst_type_nat T2 U i)
    | Forall T1 T2 ⇒ Forall (subst_type_nat T1 U i) (subst_type_nat T2 U (S i)) ].

nlet rec map A B f (l : list A) on l : list B ≝
  match l with [ nil ⇒ nil ? | cons x tl ⇒ cons ? (f x) (map ?? f tl)].
  
nlet rec foldr (A,B:Type[0]) f b (l : list A) on l : B ≝  
  match l with [ nil ⇒ b | (cons a l) ⇒ f a (foldr A B f b l)].
   
ndefinition length ≝ λT:Type.λl:list T.foldr T nat (λx,c.S c) O l.

ndefinition filter \def 
  \lambda T:Type.\lambda l:list T.\lambda p:T \to bool.
  foldr T (list T) 
    (\lambda x,l0.match (p x) with [ true => cons ? x l0 | false => l0]) (nil ?) l.


(*** definitions about lists ***)

ndefinition filter_types : list bound → list bound ≝
  λG.(filter ? G (λB.match B with [mk_bound B X T ⇒ B])).

ndefinition fv_env : list bound → list nat ≝
  λG.(map ? ? (λb.match b with [mk_bound B X T ⇒ X]) (filter_types G)).

nlet rec append A (l1: list A) l2 on l1 :=
  match l1 with
  [ nil => l2
  | (cons hd tl) => cons ? hd (append A tl l2) ].

nlet rec fv_type T ≝
  match T with
    [TVar n ⇒ nil ?
    |TFree x ⇒ cons ? x (nil ?)
    |Top ⇒ nil ?
    |Arrow U V ⇒ append ? (fv_type U) (fv_type V)
    |Forall U V ⇒ append ? (fv_type U) (fv_type V)].

(*** Type Well-Formedness judgement ***)

ninductive WFType : list bound → Typ → Prop ≝
  | WFT_TFree : ∀X,G.in_list ? X (fv_env G) → WFType G (TFree X)
  | WFT_Top : ∀G.WFType G Top
  | WFT_Arrow : ∀G,T,U.WFType G T → WFType G U → WFType G (Arrow T U)
  | WFT_Forall : ∀G,T,U.WFType G T →
                   (∀X:nat.
                    (Not (in_list ? X (fv_env G))) →
                    (Not (in_list ? X (fv_type U))) →
                    (WFType (cons ? (mk_bound true X T)  G)
                     (subst_type_nat U (TFree X) O))) → 
                 (WFType G (Forall T U)).

ninductive WFEnv : list bound → Prop ≝
  | WFE_Empty : WFEnv (nil ?)
  | WFE_cons : ∀B,X,T,G.WFEnv G → Not (in_list ? X (fv_env G)) →
                  WFType G T → WFEnv (cons ? (mk_bound B X T) G).
            
(*** Subtyping judgement ***)              
ninductive JSubtype : list bound → Typ → Typ → Prop ≝
  | SA_Top : ∀G,T.WFEnv G → WFType G T → JSubtype G T Top
  | SA_Refl_TVar : ∀G,X.WFEnv G → in_list ? X (fv_env G) 
                   → JSubtype G (TFree X) (TFree X)
  | SA_Trans_TVar : ∀G,X,T,U.in_list ? (mk_bound true X U) G →
                    JSubtype G U T → JSubtype G (TFree X) T
  | SA_Arrow : ∀G,S1,S2,T1,T2. JSubtype G T1 S1 → JSubtype G S2 T2 → 
               JSubtype G (Arrow S1 S2) (Arrow T1 T2)
  | SA_All : ∀G,S1,S2,T1,T2. JSubtype G T1 S1 →
             (∀X.Not (in_list ? X (fv_env G)) →
               JSubtype (cons ? (mk_bound true X T1) G) 
                (subst_type_nat S2 (TFree X) O) (subst_type_nat T2 (TFree X) O)) →
             JSubtype G (Forall S1 S2) (Forall T1 T2).

inductive jmeq (A:Type) (a:A) : ∀B:Type.B → Prop ≝
| refl_jmeq : jmeq A a A a. 

ninverter JS_indinv for JSubtype (%?%).

(*** ***)

ninverter dasd for pippo (?) : Type.

inductive nat : Type ≝
| O : nat 
| S : nat → nat.

inductive ppippo : nat → Prop ≝
| ppO : ppippo O
| ppSS : ∀n.ppippo n → ppippo  (S (S n)).

nlemma pippo_inv : ∀x.∀P:? → Prop.? → ? → ? → P x.
##[ (* ok, qui bisogna selezionare la meta del goal *)
   #x;#P;#H1;#H2;#H;
   napply ((λHcut:(eqn ? x x → P x).?) ?);
   ##[(* questa e` la meta cut *)
      nletin p ≝ pippo_ind;
      napply (pippo_ind (λy,p.eqn ? x y → P y) H1 H2 … H);
      (* [ * cons 1 *
         napply H1
      | * cons 2 *
         napply H2
      | * inductive term *
         napply H ] *)
   ##| napply Hcut; napply nrefl_eq]
   ##]
   ##skip;
nqed.


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

include "logic/equality.ma".
include "nat/nat.ma".
include "datatypes/bool.ma".
include "list/list.ma".
include "nat/compare.ma".
include "Fsub/util.ma".
include "Fsub/defn2.ma".

inductive NTyp : Set \def
| TName : nat \to NTyp
| NTop : NTyp
| NArrow : NTyp \to NTyp \to NTyp
| NForall : nat \to NTyp \to NTyp \to NTyp.

(*inductive NTerm : Set \def
| Name : nat \to NTerm
| NAbs : nat \to NTyp \to NTerm \to NTerm
| NApp : NTerm \to NTerm \to NTerm
| NTAbs : nat \to NTyp \to NTerm \to NTerm 
| NTApp : NTerm \to NTyp \to NTerm.*)

(*inductive LNTyp: nat \to Set \def
| LNTVar : \forall m,n.(m < n) \to LNTyp n
| LNTFree : \forall n.nat \to LNTyp n
| LNTop : \forall n.LNTyp n
| LNArrow : \forall n.(LNTyp n) \to (LNTyp n) \to (LNTyp n)
| LNForall : \forall n.(LNTyp n) \to (LNTyp (S n)) \to (LNTyp n).

inductive LNTerm : nat \to Set \def
| LNVar : \forall m,n.(m < n) \to LNTerm n
| LNFree : \forall n.nat \to LNTerm n
| LNAbs : \forall n.(LNTyp n) \to (LNTerm (S n)) \to (LNTerm n)
| LNApp : \forall n.(LNTerm n) \to (LNTerm n) \to (LNTerm n)
| LNTAbs : \forall n.(LNTyp n) \to (LNTerm (S n)) \to (LNTerm n) 
| LNTApp : \forall n.(LNTerm n) \to (LNTyp n) \to (LNTerm n).*)

record nbound : Set \def {
                           nistype : bool;
                           nname : nat;
                           nbtype : NTyp
                         }.
                         
(*record lnbound (n:nat) : Set \def {
                           lnistype : bool;
                           lnname : nat;
                           lnbtype : LNTyp n
                         }.*)
                         
inductive option (A:Type) : Set \def
| Some : A \to option A
| None : option A.

(*definition S_opt : (option nat) \to (option nat) \def
  \lambda n.match n with
  [ (Some n) \Rightarrow (Some nat (S n))
  | None \Rightarrow None nat].*)
  
(* position of the first occurrence of nat x in list l
   returns (length l) when x not in l *)
   
definition swap : nat \to nat \to nat \to nat \def
  \lambda u,v,x.match (eqb x u) with
    [true \Rightarrow v
    |false \Rightarrow match (eqb x v) with
       [true \Rightarrow u
       |false \Rightarrow x]].
       
axiom swap_left : \forall x,y.(swap x y x) = y.
(*intros;unfold swap;rewrite > eqb_n_n;simplify;reflexivity;
qed.*)

axiom swap_right : \forall x,y.(swap x y y) = x.
(*intros;unfold swap;elim (eq_eqb_case y x)
  [elim H;rewrite > H2;simplify;rewrite > H1;reflexivity
  |elim H;rewrite > H2;simplify;rewrite > eqb_n_n;simplify;reflexivity]
qed.*)

axiom swap_other : \forall x,y,z.(z \neq x) \to (z \neq y) \to (swap x y z) = z.
(*intros;unfold swap;elim (eq_eqb_case z x)
  [elim H2;lapply (H H3);elim Hletin
  |elim H2;rewrite > H4;simplify;elim (eq_eqb_case z y)
     [elim H5;lapply (H1 H6);elim Hletin
     |elim H5;rewrite > H7;simplify;reflexivity]]
qed.*)

axiom swap_inv : \forall u,v,x.(swap u v (swap u v x)) = x.
(*intros;unfold in match (swap u v x);elim (eq_eqb_case x u)
  [elim H;rewrite > H2;simplify;rewrite > H1;apply swap_right
  |elim H;rewrite > H2;simplify;elim (eq_eqb_case x v)
     [elim H3;rewrite > H5;simplify;rewrite > H4;apply swap_left
     |elim H3;rewrite > H5;simplify;apply (swap_other ? ? ? H1 H4)]]
qed.*)

axiom swap_inj : \forall u,v,x,y.(swap u v x) = (swap u v y) \to x = y.
(*intros;unfold swap in H;elim (eq_eqb_case x u)
  [elim H1;elim (eq_eqb_case y u)
     [elim H4;rewrite > H5;assumption
     |elim H4;rewrite > H3 in H;rewrite > H6 in H;simplify in H;
      elim (eq_eqb_case y v)
        [elim H7;rewrite > H9 in H;simplify in H;rewrite > H in H8;
         lapply (H5 H8);elim Hletin
        |elim H7;rewrite > H9 in H;simplify in H;elim H8;symmetry;assumption]]
  |elim H1;elim (eq_eqb_case y u)
     [elim H4;rewrite > H3 in H;rewrite > H6 in H;simplify in H;
      elim (eq_eqb_case x v)
        [elim H7;rewrite > H9 in H;simplify in H;rewrite < H in H8;
         elim H2;assumption
        |elim H7;rewrite > H9 in H;simplify in H;elim H8;assumption]
     |elim H4;rewrite > H3 in H;rewrite > H6 in H;simplify in H;
      elim (eq_eqb_case x v)
        [elim H7;rewrite > H9 in H;elim (eq_eqb_case y v)
           [elim H10;rewrite > H11;assumption
           |elim H10;rewrite > H12 in H;simplify in H;elim H5;symmetry;
            assumption]
        |elim H7;rewrite > H9 in H;elim (eq_eqb_case y v)
           [elim H10;rewrite > H12 in H;simplify in H;elim H2;assumption
           |elim H10;rewrite > H12 in H;simplify in H;assumption]]]]
qed.*)

let rec swap_NTyp u v T on T \def
  match T with
     [(TName X) \Rightarrow (TName (swap u v X))
     |NTop \Rightarrow NTop
     |(NArrow T1 T2) \Rightarrow (NArrow (swap_NTyp u v T1) (swap_NTyp u v T2))
     |(NForall X T1 T2) \Rightarrow 
                  (NForall (swap u v X) (swap_NTyp u v T1) (swap_NTyp u v T2))].

let rec swap_Typ u v T on T \def
  match T with
     [(TVar n) \Rightarrow (TVar n)
     |(TFree X) \Rightarrow (TFree (swap u v X))
     |Top \Rightarrow Top
     |(Arrow T1 T2) \Rightarrow (Arrow (swap_Typ u v T1) (swap_Typ u v T2))
     |(Forall T1 T2) \Rightarrow (Forall (swap_Typ u v T1) (swap_Typ u v T2))].
                  
definition swap_list : nat \to nat \to (list nat) \to (list nat) ≝
  \lambda u,v,l.(map ? ? (swap u v) l). 
 
let rec var_NTyp (T:NTyp):list nat\def 
  match T with 
  [TName x ⇒ [x]
  |NTop ⇒ []
  |NArrow U V ⇒ (var_NTyp U)@(var_NTyp V)
  |NForall X U V ⇒ X::(var_NTyp U)@(var_NTyp V)].

inductive alpha_eq : NTyp \to NTyp \to Prop \def
| A_refl : \forall T.(alpha_eq T T)
| A_arrow : \forall T1,T2,U1,U2.(alpha_eq T1 U1) \to (alpha_eq T2 U2) \to
                                (alpha_eq (NArrow T1 T2) (NArrow U1 U2))
| A_forall : \forall T1,T2,U1,U2,X,Y.
             (alpha_eq T1 U1) \to 
             (\forall Z.
                 \lnot (in_list nat Z (X::Y::((var_NTyp T2)@(var_NTyp U2))))
                 \to (alpha_eq (swap_NTyp Z X T2) (swap_NTyp Z Y U2))) \to
             (alpha_eq (NForall X T1 T2) (NForall Y U1 U2)).

let rec posn l x on l \def
  match l with
  [ nil \Rightarrow O
  | (cons (y:nat) l2) \Rightarrow 
      match (eqb x y) with
            [ true \Rightarrow O
            | false \Rightarrow S (posn l2 x)]].
            
let rec length A l on l \def
  match l with
    [ nil \Rightarrow O
    | (cons (y:A) l2) \Rightarrow S (length A l2)].
    
let rec lookup n l on l \def
  match l with
    [ nil ⇒ false
    | cons (x:nat) l1 \rArr match (eqb n x) with
              [true \rArr true
              |false \rArr (lookup n l1)]]. 
                             
let rec encodetype T vars on T \def
  match T with
  [ (TName n) ⇒ match (lookup n vars) with
    [ true ⇒ (TVar (posn vars n))
    | false ⇒ (TFree n)]
  | NTop ⇒ Top
  | (NArrow T1 T2) ⇒ Arrow (encodetype T1 vars) (encodetype T2 vars)
  | (NForall n2 T1 T2) ⇒ Forall (encodetype T1 vars) 
                                (encodetype T2 (n2::vars))].

let rec head (A:Type) l on l \def
  match l with
  [ nil \Rightarrow None A
  | (cons (x:A) l2) \Rightarrow Some A x].

(*let rec tail (A:Type) l \def
  match l with
  [ nil \Rightarrow nil A
  | (cons (x:A) l2) \Rightarrow l2].*)
  
let rec nth n l on n \def
  match n with
  [ O \Rightarrow match l with
    [ nil ⇒ O
    | (cons x l2) ⇒ x]
  | (S n2) \Rightarrow (nth n2 (tail ? l))]. 

definition max_list : (list nat) \to nat \def
  \lambda l.let rec aux l0 m on l0 \def
    match l0 with
      [ nil ⇒ m
      | (cons n l2) ⇒ (aux l2 (max m n))]
    in aux l O.

let rec decodetype T vars C on T \def
  match T with
  [ (TVar n) ⇒ (TName (nth n vars))
  | (TFree x)  ⇒ (TName x)
  | Top \Rightarrow NTop
  | (Arrow T1 T2) ⇒ (NArrow (decodetype T1 vars C) (decodetype T2 vars C))
  | (Forall T1 T2) ⇒ (NForall (S (max_list (vars@C))) (decodetype T1 vars C) 
       (decodetype T2 ((S (max_list (vars@C)))::vars) C))].
       
definition sublist: \forall A:Type.(list A) \to (list A) \to Prop \def
  \lambda A,l1,l2.\forall x.(in_list ? x l1) \to (in_list ? x l2).
  
let rec remove_nat (x:nat) (l:list nat) on l \def
  match l with
  [ nil ⇒ (nil nat) 
  | (cons y l2) ⇒ match (eqb x y) with
                  [ true ⇒ (remove_nat x l2)
                  | false ⇒ (y :: (remove_nat x l2)) ]].

let rec fv_NTyp (T:NTyp):list nat\def 
  match T with 
  [TName x ⇒ [x]
  |NTop ⇒ []
  |NArrow U V ⇒ (fv_NTyp U)@(fv_NTyp V)
  |NForall X U V ⇒ (fv_NTyp U)@(remove_nat X (fv_NTyp V))].
  

let rec subst_NTyp_var T X Y \def
  match T with
  [TName Z ⇒ match (eqb X Z) with
             [ true \rArr (TName Y)
             | false \rArr (TName Z) ]
  |NTop ⇒ NTop
  |NArrow U V ⇒ (NArrow (subst_NTyp_var U X Y) (subst_NTyp_var V X Y))
  |NForall Z U V ⇒ match (eqb X Z) with
                   [ true ⇒ (NForall Z (subst_NTyp_var U X Y) V)
                   | false ⇒ (NForall Z (subst_NTyp_var U X Y) 
                                        (subst_NTyp_var V X Y))]].

definition fv_Nenv : list nbound → list nat ≝
  map nbound nat
    (λb.match b with 
      [mk_nbound (B:bool) (X:nat) (T:NTyp) ⇒ X]).
          
inductive NWFType : (list nbound) → NTyp → Prop ≝
  | NWFT_TName : ∀X,G.(in_list ? X (fv_Nenv G))
                → (NWFType G (TName X))
  | NWFT_Top : ∀G.(NWFType G NTop)
  | NWFT_Arrow : ∀G,T,U.(NWFType G T) → (NWFType G U) →
                (NWFType G (NArrow T U))
  | NWFT_Forall : ∀G,X,T,U.(NWFType G T) →
                  (∀Y.¬(Y ∈ (fv_Nenv G)) →
                       (Y = X ∨ ¬(Y ∈ (fv_NTyp U))) → 
                    (NWFType ((mk_nbound true Y T) :: G) (swap_NTyp Y X U))) →
                 (NWFType G (NForall X T U)).
  (*NWFT_alpha : ∀G,T,U.(NWFType G T) → (alpha_eq T U) → (NWFType G U).*)

inductive NWFEnv : (list nbound) → Prop ≝
  | NWFE_Empty : (NWFEnv (nil ?))
  | NWFE_cons : ∀B,X,T,G.(NWFEnv G) →
                  ¬(in_list ? X (fv_Nenv G)) → 
                  (NWFType G T) → (NWFEnv ((mk_nbound B X T) :: G)).
          
inductive NJSubtype : (list nbound) → NTyp → NTyp → Prop ≝
  | NSA_Top : ∀G,T.(NWFEnv G) → (NWFType G T) → (NJSubtype G T NTop)
  | NSA_Refl_TVar : ∀G,X.(NWFEnv G)
                   → (in_list ? X (fv_Nenv G))
                   → (NJSubtype G (TName X) (TName X))
  | NSA_Trans_TVar : ∀G,X,T,U.
                     (in_list ? (mk_nbound true X U) G) →
                     (NJSubtype G U T) → (NJSubtype G (TName X) T)
  | NSA_Arrow : ∀G,S1,S2,T1,T2.
               (NJSubtype G T1 S1) → (NJSubtype G S2 T2) →
               (NJSubtype G (NArrow S1 S2) (NArrow T1 T2))
  | NSA_All : ∀G,X,Y,S1,S2,T1,T2.
              (NWFType G (NForall X S1 S2)) \to
              (NWFType G (NForall Y T1 T2)) \to
              (NJSubtype G T1 S1) →
              (∀Z.¬(Z ∈ fv_Nenv G) →
                  (Z = X \lor \lnot in_list ? Z (fv_NTyp S2)) \to
                  (Z = Y \lor \lnot in_list ? Z (fv_NTyp T2)) \to
              (NJSubtype ((mk_nbound true Z T1) :: G) 
                    (swap_NTyp Z X S2) (swap_NTyp Z Y T2))) →  
              (NJSubtype G (NForall X S1 S2) (NForall Y T1 T2))
  | NSA_alpha : ∀G,T1,T2,U1,U2.(NJSubtype G T1 U1) → 
                                (alpha_eq T1 T2) →
                                (alpha_eq U1 U2) →
                                (NJSubtype G T2 U2).
                                
let rec nt_len T \def
  match T with
  [ TName X ⇒ O
  | NTop ⇒ O
  | NArrow T1 T2 ⇒ S (max (nt_len T1) (nt_len T2))
  | NForall X T1 T2 ⇒ S (max (nt_len T1) (nt_len T2)) ].     
                
definition encodeenv : list nbound → list bound ≝
  map nbound bound 
    (λb.match b with
       [ mk_nbound b x T ⇒ mk_bound b x (encodetype T []) ]).
       
axiom append_associative : ∀A.∀l1,l2,l3:(list A).((l1@l2)@l3) = (l1@l2@l3).
       
lemma eq_fv_Nenv_fv_env : ∀G. fv_Nenv G = fv_env (encodeenv G).
intro;elim G
  [simplify;reflexivity
  |simplify;rewrite < H;elim t;simplify;reflexivity]
qed.

(* palloso *)
axiom decidable_eq_bound : \forall b,c:bound.decidable (b = c). 

lemma in_Nenv_to_in_env: ∀l,n,n2.mk_nbound true n n2 ∈ l → 
                 mk_bound true n (encodetype n2 []) ∈ encodeenv l.
intros 3;elim l
  [elim (not_in_list_nil ? ? H)
  |inversion H1;intros
     [destruct;simplify;apply in_list_head
     |destruct;elim t;simplify;apply in_list_cons;apply H;assumption]]
qed.
                 
lemma in_lookup : \forall x,l.(in_list ? x l) \to (lookup x l = true).
intros;elim H
  [simplify;rewrite > eqb_n_n;reflexivity
  |simplify;rewrite > H2;elim (eqb a a1);reflexivity]
qed.

lemma lookup_in : \forall x,l.(lookup x l = true) \to (in_list ? x l).
intros 2;elim l
  [simplify in H;destruct H
  |generalize in match H1;simplify;elim (decidable_eq_nat x t)
     [rewrite > H2;apply in_list_head
     |rewrite > (not_eq_to_eqb_false ? ? H2) in H3;simplify in H3;
      apply in_list_cons;apply H;assumption]]
qed.

lemma posn_length : \forall x,vars.(in_list ? x vars) \to 
                       (posn vars x) < (length ? vars).
intros 2;elim vars
  [elim (not_in_list_nil ? ? H)
  |inversion H1
     [intros;destruct;simplify;rewrite > eqb_n_n;simplify;
      apply lt_O_S
     |intros;destruct;simplify;elim (eqb x t);simplify
        [apply lt_O_S
        |apply le_S_S;apply H;assumption]]]
qed.

lemma in_remove : \forall a,b,l.(a \neq b) \to (in_list ? a l) \to
                                (in_list ? a (remove_nat b l)).
intros 4;elim l
  [elim (not_in_list_nil ? ? H1)
  |inversion H2;intros;
     [destruct;simplify;rewrite > not_eq_to_eqb_false
        [simplify;apply in_list_head
        |intro;apply H;symmetry;assumption]
     |destruct;simplify;elim (eqb b t)
        [simplify;apply H1;assumption
        |simplify;apply in_list_cons;apply H1;assumption]]]
qed.

axiom NTyp_len_ind : \forall P:NTyp \to Prop.
                       (\forall U.(\forall V.((nt_len V) < (nt_len U)) \to (P V))
                           \to (P U))
                       \to \forall T.(P T).
                       
axiom ntlen_arrow1 : ∀T1,T2.(nt_len T1) < (nt_len (NArrow T1 T2)). 
axiom ntlen_arrow2 : ∀T1,T2.(nt_len T2) < (nt_len (NArrow T1 T2)). 
axiom ntlen_forall1 : ∀X,T1,T2.(nt_len T1) < (nt_len (NForall X T1 T2)). 
axiom ntlen_forall2 : ∀X,T1,T2.(nt_len T2) < (nt_len (NForall X T1 T2)).
axiom eq_ntlen_swap : ∀X,Y,T.nt_len T = nt_len (swap_NTyp X Y T).

axiom nat_in_list_case :\forall G:list nat
.\forall H:list nat
 .\forall n:nat.in_list nat n (H@G)\rarr in_list nat n G\lor in_list nat n H.
 
lemma swap_same : \forall x,y.swap x x y = y.
intros;elim (decidable_eq_nat y x)
  [autobatch paramodulation
  |rewrite > swap_other;autobatch]
qed.

lemma not_nat_in_to_lookup_false : ∀l,X.¬(X ∈ l) → lookup X l = false.
intros 2;elim l
  [simplify;reflexivity
  |simplify;elim (decidable_eq_nat X t)
     [elim H1;rewrite > H2;apply in_list_head
     |rewrite > (not_eq_to_eqb_false ? ? H2);simplify;apply H;intro;apply H1;
      apply (in_list_cons ? ? ? ? H3);]]
qed.

lemma fv_encode : ∀T,l1,l2.
                  (∀x.(in_list ? x (fv_NTyp T)) →
                     (lookup x l1 = lookup x l2 ∧
                     (lookup x l1 = true → posn l1 x = posn l2 x))) →
                  (encodetype T l1 = encodetype T l2).
intro;elim T
  [simplify in H;elim (H n)
     [simplify;rewrite < H1;generalize in match H2;elim (lookup n l1)
        [simplify;rewrite > H3;autobatch
        |simplify;reflexivity]
     |apply in_list_head]
  |simplify;reflexivity
  |simplify;rewrite > (H l1 l2)
     [rewrite > (H1 l1 l2)
        [reflexivity
        |intros;apply H2;simplify;apply in_list_to_in_list_append_r;autobatch]
     |intros;apply H2;simplify;apply in_list_to_in_list_append_l;autobatch]
  |simplify;rewrite > (H l1 l2)
     [rewrite > (H1 (n::l1) (n::l2))
        [reflexivity
        |intros;elim (decidable_eq_nat x n)
           [simplify;rewrite > (eq_to_eqb_true ? ? H4);simplify;split
              [reflexivity|intro;reflexivity]
           |elim (H2 x)
              [split
                 [simplify;rewrite < H5;reflexivity
                 |simplify;elim (eqb x n);
                    [simplify;reflexivity
                    |simplify in H7;rewrite < (H6 H7);reflexivity]]
              |simplify;apply in_list_to_in_list_append_r;
               apply (in_remove ? ? ? H4);assumption]]]
     |intros;apply H2;simplify;apply in_list_to_in_list_append_l;autobatch]]
qed.

lemma lookup_swap : \forall a,b,x,vars.
                    (lookup (swap a b x) (swap_list a b vars) =
                    lookup x vars).
intros 4;elim vars
  [simplify;reflexivity
  |simplify;elim (decidable_eq_nat x t)
     [rewrite > H1;rewrite > eqb_n_n;rewrite > eqb_n_n;simplify;reflexivity
     |rewrite > (not_eq_to_eqb_false ? ? H1);elim (decidable_eq_nat x a)
        [rewrite > H;rewrite > H2;rewrite > swap_left;
         elim (decidable_eq_nat b t)
           [rewrite < H3;rewrite > swap_right;
            rewrite > (not_eq_to_eqb_false b a)
              [reflexivity
              |intro;autobatch]
           |rewrite > (swap_other a b t)
              [rewrite > (not_eq_to_eqb_false ? ? H3);simplify;reflexivity
              |intro;autobatch
              |intro;autobatch]]
        |elim (decidable_eq_nat x b)
           [rewrite > H;rewrite > H3;rewrite > swap_right;
            elim (decidable_eq_nat t a)
              [rewrite > H4;rewrite > swap_left;
               rewrite > (not_eq_to_eqb_false a b)
                 [reflexivity
                 |intro;autobatch]
              |rewrite > (swap_other a b t)
                 [rewrite > (not_eq_to_eqb_false a t)
                    [reflexivity
                    |intro;autobatch]
                 |assumption
                 |intro;autobatch]]
           |rewrite > H;rewrite > (swap_other a b x)
              [elim (decidable_eq_nat a t)
                 [rewrite > H4;rewrite > swap_left;
                  rewrite > (not_eq_to_eqb_false ? ? H3);reflexivity
                 |elim (decidable_eq_nat b t)
                    [rewrite > H5;rewrite > swap_right;
                     rewrite > (not_eq_to_eqb_false ? ? H2);reflexivity
                    |rewrite > (swap_other a b t)
                       [rewrite > (not_eq_to_eqb_false ? ? H1);reflexivity
                       |intro;autobatch
                       |intro;autobatch]]]
              |assumption
              |assumption]]]]]
qed.

lemma posn_swap : \forall a,b,x,vars.
                  (posn vars x = posn (swap_list a b vars) (swap a b x)).
intros 4;elim vars
  [simplify;reflexivity
  |simplify;rewrite < H;elim (decidable_eq_nat x t)
     [rewrite > H1;do 2 rewrite > eqb_n_n;reflexivity
     |elim (decidable_eq_nat (swap a b x) (swap a b t))
        [elim H1;autobatch
        |rewrite > (not_eq_to_eqb_false ? ? H1);
         rewrite > (not_eq_to_eqb_false ? ? H2);reflexivity]]]
qed.   

theorem encode_swap : ∀a,x,T,vars.
                         ((in_list ? a (fv_NTyp T)) → (in_list ? a vars)) →
                         (in_list ? x vars) →
                      encodetype T vars = 
                      encodetype (swap_NTyp a x T) (swap_list a x vars).
intros 3;elim T
  [elim (decidable_eq_nat n x)
     [rewrite > H2;simplify in match (swap_NTyp ? ? ?);rewrite > swap_right;
      simplify;lapply (lookup_swap a x x vars);rewrite > swap_right in Hletin;
      rewrite > Hletin;cut ((in_list ? x vars) \to (lookup x vars = true)) 
        [rewrite > (Hcut H1);simplify;lapply (posn_swap a x x vars);
         rewrite > swap_right in Hletin1;rewrite < Hletin1;reflexivity
        |generalize in match x;elim vars
           [elim (not_in_list_nil ? ? H3)
           |inversion H4
              [intros;simplify;rewrite > eqb_n_n;reflexivity
              |intros;simplify;destruct;rewrite > (H3 ? H5);
               elim (eqb n1 t);reflexivity]]]
     |elim (decidable_eq_nat n a);
        [rewrite < H3;simplify;rewrite < posn_swap;rewrite > lookup_swap;
         rewrite < H3 in H;simplify in H;rewrite > in_lookup;
           [simplify;reflexivity
           |apply H;apply in_list_head]
        |simplify in ⊢ (? ? ? (? % ?));rewrite > swap_other;
           [apply (fv_encode ? vars (swap_list a x vars));intros;
            simplify in H4;cut (x1 = n)
              [rewrite > Hcut;elim vars
                 [simplify;split [reflexivity|intro;reflexivity]
                 |simplify;elim H5;cut
                    (t = a ∨t = x ∨ (t ≠ a ∧ t ≠ x))
                    [|elim (decidable_eq_nat t a)
                       [left;left;assumption
                       |elim (decidable_eq_nat t x)
                          [left;right;assumption
                          |right;split;assumption]]]
                  elim Hcut1
                    [elim H8
                       [rewrite > H9;rewrite > swap_left;
                        rewrite > (not_eq_to_eqb_false ? ? H2); 
                        rewrite > (not_eq_to_eqb_false ? ? H3);simplify;
                        split
                          [assumption
                          |intro;rewrite < (H7 H10);reflexivity]
                       |rewrite > H9;rewrite > swap_right; 
                        rewrite > (not_eq_to_eqb_false ? ? H2); 
                        rewrite > (not_eq_to_eqb_false ? ? H3);simplify;
                        split
                          [assumption
                          |intro;rewrite < (H7 H10);reflexivity]]
                    |elim H8;rewrite > (swap_other a x t)
                       [rewrite < H6;split
                          [reflexivity
                          |elim (eqb n t)
                             [simplify;reflexivity
                             |simplify in H11;rewrite < (H7 H11);reflexivity]]
                       |*:assumption]]]
              |inversion H4
                 [intros;destruct;reflexivity
                 |intros;destruct;elim (not_in_list_nil ? ? H5)]]
           |*:assumption]]]
  |simplify;reflexivity
  |simplify;simplify in H2;rewrite < H
     [rewrite < H1
        [reflexivity
        |intro;apply H2;apply in_list_to_in_list_append_r;autobatch
        |assumption]
     |intro;apply H2;apply in_list_to_in_list_append_l;autobatch
     |assumption]
  |simplify;simplify in H2;rewrite < H
     [elim (decidable_eq_nat a n)
        [rewrite < (H1 (n::vars));
           [reflexivity
           |intro;rewrite > H4;apply in_list_head
           |apply in_list_cons;assumption]
        |rewrite < (H1 (n::vars));
           [reflexivity
           |intro;apply in_list_cons;apply H2;apply in_list_to_in_list_append_r;
            apply (in_remove ? ? ? H4 H5)
           |apply in_list_cons;assumption]]
     |intro;apply H2;apply in_list_to_in_list_append_l;assumption
     |assumption]]
qed.

lemma encode_swap2 : ∀a:nat.∀x:nat.∀T:NTyp.
  ¬(a ∈ (fv_NTyp T)) →
    \forall vars.x ∈ vars
       →encodetype T vars=encodetype (swap_NTyp a x T) (swap_list a x vars).
intros;apply (encode_swap ? ? ? ? ? H1);intro;elim (H H2);
qed.

lemma remove_inlist : \forall x,y,l.(in_list ? x (remove_nat y l)) \to
                      (in_list ? x l) \land x \neq y.
intros 3;elim l 0
  [simplify;intro;elim (not_in_list_nil ? ? H)
  |simplify;intro;elim (decidable_eq_nat y t)
     [rewrite > H in H2;rewrite > eqb_n_n in H2;simplify in H2;
      rewrite > H in H1;elim (H1 H2);rewrite > H;split
        [apply in_list_cons;assumption
        |assumption]
     |rewrite > (not_eq_to_eqb_false ? ? H) in H2;simplify in H2;
      inversion H2
        [intros;destruct;split
           [apply in_list_head
           |intro;autobatch] 
        |intros;destruct;
         elim (H1 H3);split
           [apply in_list_cons;assumption
           |assumption]]]]
qed.

lemma inlist_remove : \forall x,y,l.(in_list ? x l \to x \neq y \to 
                (in_list ? x (remove_nat y l))).
intros 3;elim l
  [elim (not_in_list_nil ? ? H);
  |simplify;elim (decidable_eq_nat y t)
     [rewrite > (eq_to_eqb_true ? ? H3);simplify;apply H
        [(*FIXME*)generalize in match H1;intro;inversion H1
           [intros;destruct;elim H2;reflexivity
           |intros;destruct;assumption]
        |assumption]
     |rewrite > (not_eq_to_eqb_false ? ? H3);simplify;
      (*FIXME*)generalize in match H1;intro;inversion H4
        [intros;destruct;apply in_list_head
        |intros;destruct;apply in_list_cons;apply (H H5 H2)
        ]]]
qed.

lemma incl_fv_var : \forall T.(incl ? (fv_NTyp T) (var_NTyp T)).
intro;elim T
  [simplify;unfold;intros;assumption
  |simplify;unfold;intros;assumption
  |simplify;unfold;intros;elim (in_list_append_to_or_in_list ? ? ? ? H2)
     [apply in_list_to_in_list_append_l;apply (H ? H3)
     |apply in_list_to_in_list_append_r;apply (H1 ? H3)]
  |simplify;unfold;intros;elim (decidable_eq_nat x n)
     [rewrite > H3;apply in_list_head
     |apply in_list_cons;elim (in_list_append_to_or_in_list ? ? ? ? H2)
        [apply in_list_to_in_list_append_l;apply (H ? H4)
        |apply in_list_to_in_list_append_r;elim (remove_inlist ? ? ? H4);
         apply (H1 ? H5)]]]
qed.

lemma fv_encode2 : ∀T,l1,l2.
                      (∀x.(in_list ? x (fv_NTyp T)) →
                           (lookup x l1 = lookup x l2 ∧
                            posn l1 x = posn l2 x)) →
                      (encodetype T l1 = encodetype T l2).
intros;apply fv_encode;intros;elim (H ? H1);split
  [assumption|intro;assumption]
qed.

lemma alpha_sym : \forall S,T.(alpha_eq S T) \to (alpha_eq T S).
intros;elim H
  [apply A_refl
  |apply A_arrow;assumption
  |apply A_forall
     [assumption
     |intros;apply H4;intro;apply H5;elim (decidable_eq_nat Z n5)
        [rewrite > H7;apply in_list_head
        |apply in_list_cons;(*FIXME*)generalize in match H6;intro;
         inversion H6
           [intros;destruct;apply in_list_head
           |intros;destruct;apply in_list_cons;inversion H9
              [intros;destruct;elim H7;reflexivity
              |intros;destruct;
               elim (in_list_append_to_or_in_list ? ? ? ? H11)
                 [apply in_list_to_in_list_append_r;assumption
                 |apply in_list_to_in_list_append_l;assumption]]]]]]
qed.

lemma inlist_fv_swap : \forall x,y,b,T.
                   (\lnot (in_list ? b (y::var_NTyp T))) \to
                   (in_list ? x (fv_NTyp (swap_NTyp b y T))) \to
                   (x \neq y \land (x = b \lor (in_list ? x (fv_NTyp T)))).
intros 4;elim T
  [simplify in H;simplify;simplify in H1;elim (decidable_eq_nat y n)
     [rewrite > H2 in H1;rewrite > swap_right in H1;
      inversion H1
        [intros;destruct;split
           [unfold;intro;apply H;rewrite > H2;apply in_list_head
           |left;reflexivity]
        |intros;destruct;elim (not_in_list_nil ? ? H3)]
     |elim (decidable_eq_nat b n)
        [rewrite > H3 in H;elim H;apply in_list_cons;apply in_list_head
        |rewrite > swap_other in H1
           [split
              [inversion H1
                 [intros;destruct;intro;apply H2;
                  symmetry;assumption
                 |intros;destruct;
                  elim (not_in_list_nil ? ? H4)]
              |autobatch]
           |intro;autobatch
           |intro;autobatch]]]
  |simplify in H1;elim (not_in_list_nil ? ? H1)
  |simplify;simplify in H3;simplify in H2;elim (nat_in_list_case ? ? ? H3)
     [elim H1
        [split
           [assumption
           |elim H6
              [left;assumption
              |right;apply in_list_to_in_list_append_r;assumption]]
           |intro;apply H2;elim (nat_in_list_case (var_NTyp n1) [y] ? H5)
              [apply (in_list_to_in_list_append_r ? ? (y::var_NTyp n) (var_NTyp n1));
               assumption
              |inversion H6
                 [intros;destruct;apply in_list_head
                 |intros;destruct;
                  elim (not_in_list_nil ? ? H7)]]
           |assumption]
        |elim H
           [split
              [assumption
              |elim H6
                 [left;assumption
                 |right;apply in_list_to_in_list_append_l;assumption]]
           |intro;apply H2;inversion H5
              [intros;destruct;apply in_list_head
              |intros;destruct;apply in_list_cons;
               apply in_list_to_in_list_append_l;assumption]
           |assumption]]
   |simplify;simplify in H3;simplify in H2;elim (nat_in_list_case ? ? ? H3)
      [elim H1
         [split
            [assumption
            |elim H6
               [left;assumption
               |right;apply in_list_to_in_list_append_r;apply inlist_remove
                  [assumption
                  |intro;elim (remove_inlist ? ? ? H4);apply H10;
                   rewrite > swap_other
                     [assumption
                     |intro;rewrite > H8 in H7;rewrite > H11 in H7;apply H2;
                      destruct;apply in_list_cons;apply in_list_head
                     |destruct;assumption]]]]
         |intro;apply H2;inversion H5
            [intros;destruct;apply in_list_head
            |intros;destruct;
             apply in_list_cons;
             cut ((n::var_NTyp n1)@(var_NTyp n2) = n::var_NTyp n1@var_NTyp n2)
               [rewrite < Hcut;elim (n::var_NTyp n1)
                  [simplify;assumption
                  |simplify;elim (decidable_eq_nat b t)
                     [rewrite > H9;apply in_list_head
                     |apply in_list_cons;assumption]]
               |simplify;reflexivity]]
         |elim(remove_inlist ? ? ? H4);assumption]
      |elim H
         [split
            [assumption
            |elim H6
               [left;assumption
                  |right;apply in_list_to_in_list_append_l;
                   assumption]]
            |intro;apply H2;inversion H5
               [intros;destruct;apply in_list_head
               |intros;destruct;apply in_list_cons;
                elim (decidable_eq_nat b n)
                  [rewrite > H8;apply in_list_head
                  |apply in_list_cons;apply in_list_to_in_list_append_l;
                   assumption]]
            |assumption]]]
qed.

lemma inlist_fv_swap_r : \forall x,y,b,T.
                   (\lnot (in_list ? b (y::var_NTyp T))) \to
                   ((x = b \land (in_list ? y (fv_NTyp T))) \lor
                    (x \neq y \land (in_list ? x (fv_NTyp T)))) \to
                   (in_list ? x (fv_NTyp (swap_NTyp b y T))).
intros 4;elim T
  [simplify;simplify in H;simplify in H1;cut (b \neq n)
     [elim H1
        [elim H2;cut (y = n)
           [rewrite > Hcut1;rewrite > swap_right;rewrite > H3;apply in_list_head
           |inversion H4
              [intros;destruct;autobatch
              |intros;destruct;elim (not_in_list_nil ? ? H5)]]
        |elim H2;inversion H4
           [intros;destruct;rewrite > (swap_other b y x)
              [apply in_list_head
              |intro;autobatch
              |assumption]
           |intros;destruct;elim (not_in_list_nil ? ? H5)]]
        |intro;apply H;apply (in_list_to_in_list_append_r ? ? [y] [n]);
         rewrite > H2;apply in_list_head]
  |simplify in H1;elim H1;elim H2;elim (not_in_list_nil ? ? H4)
  |simplify;simplify in H3;cut (\lnot (in_list ? b (y::var_NTyp n1)))
     [cut (\lnot (in_list ? b (y::var_NTyp n)))
        [elim H3
           [elim H4;elim (in_list_append_to_or_in_list ? ? ? ? H6)
              [apply in_list_to_in_list_append_l;apply H
                 [assumption
                 |left;split;assumption]
              |apply in_list_to_in_list_append_r;apply H1
                 [assumption
                 |left;split;assumption]]
           |elim H4;elim (in_list_append_to_or_in_list ? ? ? ? H6)
              [apply in_list_to_in_list_append_l;apply H;
                 [assumption
                 |right;split;assumption]
              |apply in_list_to_in_list_append_r;apply H1
                 [assumption
                 |right;split;assumption]]]
        |intro;apply H2;inversion H4
           [intros;destruct;apply in_list_head
           |intros;destruct;apply in_list_cons;
            simplify;apply in_list_to_in_list_append_l;
            assumption]]
     |intro;apply H2;inversion H4
        [intros;destruct;apply in_list_head
        |intros;destruct;apply in_list_cons;
         simplify;apply in_list_to_in_list_append_r;
         assumption]]
  |simplify;simplify in H3;cut (\lnot (in_list ? b (y::var_NTyp n1)))
     [cut (\lnot (in_list ? b (y::var_NTyp n2)))
        [elim H3
           [elim H4;elim (in_list_append_to_or_in_list ? ? ? ? H6)
              [apply in_list_to_in_list_append_l;apply H
                 [assumption
                 |left;split;assumption]
              |apply in_list_to_in_list_append_r;apply inlist_remove
                 [apply H1;
                    [assumption
                    |left;split
                       [assumption|elim (remove_inlist ? ? ? H7);assumption]]
                 |elim (remove_inlist ? ? ? H7);elim (decidable_eq_nat b n)
                    [rewrite > H10;rewrite > swap_left;intro;apply H9;
                     rewrite < H11;rewrite < H10;assumption
                    |rewrite > swap_other
                       [rewrite > H5;assumption
                       |intro;apply H10;symmetry;assumption
                       |intro;apply H9;symmetry;assumption]]]]
           |elim H4;elim (in_list_append_to_or_in_list ? ? ? ? H6)
              [apply in_list_to_in_list_append_l;apply H
                 [assumption
                 |right;split;assumption]
              |apply in_list_to_in_list_append_r;apply inlist_remove
                 [apply H1;
                    [assumption
                    |right;split
                       [assumption|elim (remove_inlist ? ? ? H7);assumption]]
                 |elim (decidable_eq_nat b n)
                    [rewrite > H8;rewrite > swap_left;assumption
                    |elim (decidable_eq_nat y n)
                       [rewrite > H9;rewrite > swap_right;intro;apply Hcut1;
                        rewrite > H9;apply in_list_cons;
                        apply incl_fv_var;elim (remove_inlist ? ? ? H7);
                        rewrite < H10;assumption
                       |rewrite > (swap_other b y n)
                          [elim (remove_inlist ? ? ? H7);assumption
                          |intro;autobatch
                          |intro;autobatch]]]]]]
        |intro;apply H2;inversion H4
           [intros;destruct;apply in_list_head
           |simplify;intros;destruct;
            apply in_list_cons;
            apply (in_list_to_in_list_append_r ? ? (n::var_NTyp n1) (var_NTyp n2));
            assumption]]
     |intro;apply H2;inversion H4
        [intros;destruct;apply in_list_head
        |simplify;intros;destruct;
         apply in_list_cons;
         apply (in_list_to_in_list_append_l ? ? (n::var_NTyp n1) (var_NTyp n2));
         apply in_list_cons;assumption]]]
qed.               

lemma fv_alpha : \forall S,T.(alpha_eq S T) \to 
                 (incl ? (fv_NTyp S) (fv_NTyp T)).
intros;elim H
  [unfold;intros;assumption
  |simplify;unfold;intros;elim (in_list_append_to_or_in_list ? ? ? ? H5)
     [apply in_list_to_in_list_append_l;autobatch
     |apply in_list_to_in_list_append_r;autobatch]
  |simplify;unfold;intros;
   elim (in_list_append_to_or_in_list ? ? ? ? H5)
     [apply in_list_to_in_list_append_l;apply (H2 ? H6)
     |elim (fresh_name (n4::n5::var_NTyp n1@var_NTyp n3));
      apply in_list_to_in_list_append_r; 
      lapply (H4 ? H7);
      elim (remove_inlist ? ? ? H6);apply inlist_remove
        [lapply (inlist_fv_swap_r x n4 a n1) 
           [elim (inlist_fv_swap x n5 a n3)
              [elim H11
                 [rewrite < H12 in H7;elim H7;
                  do 2 apply in_list_cons;
                  apply in_list_to_in_list_append_l;
                  apply (incl_fv_var n1 ? H8);
                 |assumption]
              |intro;apply H7;inversion H10;intros;destruct;
                 [apply in_list_cons;apply in_list_head
                 |do 2 apply in_list_cons;apply in_list_to_in_list_append_r;
                  assumption]
              |apply (Hletin ? Hletin1)]
           |intro;apply H7;inversion H10
              [intros;destruct;apply in_list_head
              |intros;destruct;do 2 apply in_list_cons;
               apply in_list_to_in_list_append_l;assumption]
           |right;split;assumption]
        |intros;intro;lapply (inlist_fv_swap_r x n4 a n1)
           [lapply (Hletin ? Hletin1);
            elim (inlist_fv_swap x n5 a n3 ? Hletin2)
              [apply (H11 H10)
              |intro;apply H7;elim (decidable_eq_nat a n4)
                 [rewrite > H12;apply in_list_head
                 |apply in_list_cons;inversion H11;intros;destruct;
                    [apply in_list_head
                    |apply in_list_cons;apply in_list_to_in_list_append_r;
                     assumption]]]
           |intro;apply H7;inversion H11
              [intros;destruct;apply in_list_head
              |intros;destruct;do 2 apply in_list_cons;
               apply in_list_to_in_list_append_l;assumption]
           |right;split;assumption]]]]
qed.

theorem alpha_to_encode : ∀S,T.(alpha_eq S T) → 
                             ∀vars.(encodetype S vars) = (encodetype T vars).
intros 3;elim H
  [reflexivity
  |simplify;rewrite > H2;rewrite > H4;reflexivity
  |simplify;rewrite > H2;
   cut (encodetype n1 (n4::vars) = encodetype n3 (n5::vars))
     [rewrite > Hcut;reflexivity
     |elim (fresh_name (n4::n5::var_NTyp n1@var_NTyp n3));
      lapply (encode_swap2 a n4 n1 ? (n4::vars))
        [intro;apply H5;do 2 apply in_list_cons;
         apply in_list_to_in_list_append_l;autobatch
        |lapply (encode_swap2 a n5 n3 ? (n5::vars))
           [intro;apply H5;do 2 apply in_list_cons;
            apply in_list_to_in_list_append_r;autobatch 
           |rewrite > Hletin;rewrite > Hletin1;simplify;rewrite > swap_right;
            rewrite > swap_right;rewrite > (H4 a H5 (a::swap_list a n4 vars));
            rewrite > (fv_encode2 ? ? (a::swap_list a n5 vars))
              [reflexivity
              |intros;elim (decidable_eq_nat n4 n5)
                 [rewrite > H7;autobatch
                 |cut ((x \neq n4) \land (x \neq n5))
                    [elim Hcut;elim (decidable_eq_nat x a)
                       [simplify;rewrite > (eq_to_eqb_true ? ? H10);simplify;
                        autobatch
                       |simplify;rewrite > (not_eq_to_eqb_false ? ? H10);
                        simplify;elim vars
                             [simplify;autobatch
                             |simplify;elim H11;rewrite < H12;
                              rewrite > H13;elim (decidable_eq_nat a t)
                                [rewrite > H14;rewrite > swap_left;
                                 rewrite > swap_left;
                                 rewrite > (not_eq_to_eqb_false ? ? H8);  
                                 rewrite > (not_eq_to_eqb_false ? ? H9);
                                 simplify;autobatch
                                |elim (decidable_eq_nat n4 t)
                                   [rewrite > H15;rewrite > swap_right;
                                    rewrite > (swap_other a n5 t)
                                       [rewrite > (not_eq_to_eqb_false ? ? H10);
                                        rewrite < H15;
                                        rewrite > (not_eq_to_eqb_false ? ? H8);
                                        autobatch
                                       |intro;autobatch
                                       |intro;apply H7;autobatch]
                                   |rewrite > (swap_other a n4 t);
                                    elim (decidable_eq_nat n5 t)
                                      [rewrite < H16;rewrite > swap_right;
                                    rewrite > (not_eq_to_eqb_false ? ? H9);
                                    rewrite > (not_eq_to_eqb_false ? ? H10);
                                    autobatch
                                   |rewrite > (swap_other a n5 t);try intro;
                                    autobatch
                                   |*:intro;autobatch]]]]]
                       |split
                          [lapply (H3 ? H5);lapply (alpha_sym ? ? Hletin2);
                           lapply (fv_alpha ? ? Hletin3);
                           lapply (Hletin4 ? H6);
                           elim (inlist_fv_swap ? ? ? ? ? Hletin5)
                             [assumption
                             |intro;apply H5;inversion H8
                                [intros;destruct;
                                 apply in_list_head
                                |intros;destruct;
                                 do 2 apply in_list_cons;
                                 apply in_list_to_in_list_append_l;assumption]]
                          |elim (inlist_fv_swap ? ? ? ? ? H6)
                             [assumption
                             |intro;apply H5;elim (decidable_eq_nat a n4)
                                [rewrite > H9;apply in_list_head
                                |apply in_list_cons;
                                 inversion H8;intros;destruct;
                                   [apply in_list_head
                                   |apply in_list_cons;
                                    apply in_list_to_in_list_append_r;
                                    assumption]]]]]]]
              |apply in_list_head]
           |apply in_list_head]]]
qed.
                      
lemma encode_append : ∀T,U,n,l.length ? l ≤ n →
        subst_type_nat (encodetype T l) U n = encodetype T l.
intros 2;elim T
  [simplify;elim (bool_to_decidable_eq (lookup n l) true)
     [rewrite > H1;simplify;lapply (lookup_in ? ? H1);
      lapply (posn_length ? ? Hletin);
      cut (posn l n ≠ n1)
        [rewrite > (not_eq_to_eqb_false ? ? Hcut);simplify;reflexivity
        |intro;rewrite > H2 in Hletin1;unfold in Hletin1;autobatch;]
     |cut (lookup n l = false)
        [rewrite > Hcut;reflexivity
        |generalize in match H1;elim (lookup n l);
           [elim H2;reflexivity|reflexivity]]]
  |simplify;reflexivity
  |simplify;autobatch
  |simplify;rewrite > (H ? ? H2);rewrite > H1
     [reflexivity
     |simplify;autobatch]]
qed.

lemma encode_subst_simple : ∀X,T,l.
     (encodetype T l = subst_type_nat (encodetype T (l@[X])) (TFree X) (length ? l)).
intros 2;elim T
  [simplify;cut (lookup n l = true → posn l n = posn (l@[X]) n)
     [generalize in match Hcut;elim (bool_to_decidable_eq (lookup n l) true)
        [cut (lookup n (l@[X]) = true)
           [rewrite > H;rewrite > Hcut1;simplify;
            cut (eqb (posn (l@[X]) n) (length nat l) = false)
              [rewrite > Hcut2;simplify;rewrite < (H1 H);reflexivity
              |generalize in match H;elim l 0
                 [simplify;intro;destruct H2
                 |intros 2;simplify;elim (eqb n t)
                    [simplify;reflexivity
                    |simplify in H3;simplify;apply (H2 H3)]]]
           |generalize in match H;elim l
              [simplify in H2;destruct H2
              |generalize in match H3;simplify;elim (eqb n t) 0
                 [simplify;intro;reflexivity
                 |simplify;intro;apply (H2 H4)]]]
        |cut (lookup n l = false)
           [elim (decidable_eq_nat n X)
              [rewrite > Hcut1;rewrite > H2;cut (lookup X (l@[X]) = true)
                 [rewrite > Hcut2;simplify;
                  cut (eqb (posn (l@[X]) X) (length nat l) = true)
                    [rewrite > Hcut3;simplify;reflexivity
                    |generalize in match Hcut1;elim l 0
                       [intros;simplify;rewrite > eqb_n_n;simplify;reflexivity
                       |simplify;intros 2;rewrite > H2;elim (eqb X t)
                          [simplify in H4;destruct H4
                          |simplify;simplify in H4;apply (H3 H4)]]]
                 |elim l
                    [simplify;rewrite > eqb_n_n;reflexivity
                    |simplify;elim (eqb X t)
                       [simplify;reflexivity
                       |simplify;assumption]]]
              |cut (lookup n l = lookup n (l@[X]))
                 [rewrite < Hcut2;rewrite > Hcut1;simplify;reflexivity
                 |elim l
                    [simplify;rewrite > (not_eq_to_eqb_false ? ? H2);simplify;
                     reflexivity
                    |simplify;elim (eqb n t)
                       [simplify;reflexivity
                       |simplify;assumption]]]]
           |generalize in match H;elim (lookup n l);
              [elim H2;reflexivity|reflexivity]]]
     |elim l 0
        [intro;simplify in H;destruct H
        |simplify;intros 2;elim (eqb n t)
           [simplify;reflexivity
           |simplify in H1;simplify;rewrite < (H H1);reflexivity]]]
  |simplify;reflexivity
  |simplify;rewrite < H;rewrite < H1;reflexivity
  |simplify;rewrite < H;rewrite < (append_associative ? [n] l [X]);
   rewrite < (H1 ([n]@l));reflexivity]
qed.

lemma encode_subst : ∀T,X,Y,l.¬(X ∈ l) → ¬(Y ∈ l) →
                              (X ∈ (fv_NTyp T) → X = Y) → 
                              encodetype (swap_NTyp X Y T) l =
                 subst_type_nat (encodetype T (l@[Y])) (TFree X) (length ? l).
apply NTyp_len_ind;intro;elim U
  [elim (decidable_eq_nat n X)
     [rewrite > H4 in H3;rewrite > H4;rewrite > H3
        [simplify in \vdash (? ? (? % ?) ?);rewrite > swap_same;
         cut (lookup Y (l@[Y]) = true)
           [simplify;rewrite > Hcut;rewrite > (not_nat_in_to_lookup_false ? ? H2);
            simplify;cut (posn (l@[Y]) Y = length ? l)
              [rewrite > Hcut1;rewrite > eqb_n_n;reflexivity
              |generalize in match H2;elim l;simplify
                 [rewrite > eqb_n_n;reflexivity
                 |elim (decidable_eq_nat Y t)
                    [elim H6;rewrite > H7;apply in_list_head
                    |rewrite > (not_eq_to_eqb_false ? ? H7);simplify;
                     rewrite < H5
                       [reflexivity
                       |intro;apply H6;apply in_list_cons;assumption]]]]
           |elim l
              [simplify;rewrite > eqb_n_n;reflexivity
              |simplify;rewrite > H5;elim (eqb Y t);reflexivity]]
        |simplify;apply in_list_head]
     |elim (decidable_eq_nat Y n);
        [rewrite < H5;simplify;rewrite > swap_right;
         rewrite > (not_nat_in_to_lookup_false ? ? H1);
         cut (lookup Y (l@[Y]) = true)
           [rewrite > Hcut;simplify;cut (posn (l@[Y]) Y = length ? l)
              [rewrite > Hcut1;rewrite > eqb_n_n;reflexivity
              |generalize in match H2;elim l;simplify
                 [rewrite > eqb_n_n;reflexivity
                 |elim (decidable_eq_nat Y t)
                    [elim H7;rewrite > H8;apply in_list_head
                    |rewrite > (not_eq_to_eqb_false ? ? H8);simplify;
                     rewrite < H6
                       [reflexivity
                       |intro;apply H7;apply in_list_cons;assumption]]]]
           |elim l;simplify
                 [rewrite > eqb_n_n;reflexivity
                 |elim (eqb Y t);simplify;autobatch]]
        |simplify;rewrite > (swap_other X Y n)
           [cut (lookup n l = lookup n (l@[Y]) ∧ 
                 (lookup n l = true → posn l n = posn (l@[Y]) n))
              [elim Hcut;rewrite > H6;generalize in match H7;
               generalize in match H6;elim (lookup n (l@[Y]))
                 [simplify;rewrite < H9;generalize in match H8;elim l
                    [simplify in H10;destruct H10
                    |elim (decidable_eq_nat n t)
                       [simplify;rewrite > (eq_to_eqb_true ? ? H12);simplify;
                        reflexivity
                       |simplify;rewrite > (not_eq_to_eqb_false ? ? H12);
                        simplify;generalize in match H10;
                        elim (eqb (posn l1 n) (length nat l1))
                          [simplify in H13;simplify in H11;
                           rewrite > (not_eq_to_eqb_false ? ? H12) in H11;
                           simplify in H11;lapply (H13 H11);destruct Hletin
                          |simplify;reflexivity]]
                    |assumption
                    |assumption]
                 |simplify;reflexivity]
              |elim l;split
                 [simplify;cut (n ≠ Y)
                    [rewrite > (not_eq_to_eqb_false ? ? Hcut);simplify;
                     reflexivity
                    |intro;apply H5;symmetry;assumption]
                 |intro;simplify in H6;destruct H6
                 |elim H6;simplify;rewrite < H7;reflexivity
                 |simplify;elim (eqb n t)
                    [simplify;reflexivity
                    |simplify;simplify in H7;elim H6;rewrite < (H9 H7);
                     reflexivity]]]
           |assumption
           |intro;apply H5;symmetry;assumption]]]
  |simplify;reflexivity
  |simplify;rewrite < (H2 n ? ? ? ? H3 H4) 
     [rewrite < (H2 n1 ? ? ? ? H3 H4);
        [autobatch|autobatch
        |intro;apply H5;simplify;apply in_list_to_in_list_append_r;assumption]
     |autobatch
     |intro;apply H5;simplify;apply in_list_to_in_list_append_l;assumption]
  |simplify;rewrite < (H2 n1 ? ? ? ? H3 H4) 
     [cut (l = swap_list X Y l)
           [|generalize in match H3;generalize in match H4;elim l
               [simplify;reflexivity
               |simplify;elim (decidable_eq_nat t X)
                  [elim H8;rewrite > H9;apply in_list_head
                  |elim (decidable_eq_nat t Y)
                     [elim H7;rewrite > H10;apply in_list_head
                     |rewrite > (swap_other X Y t)
                        [rewrite < H6
                           [reflexivity
                           |intro;apply H7;apply in_list_cons;assumption
                           |intro;apply H8;apply in_list_cons;assumption]
                        |*:assumption]]]]]
      elim (decidable_eq_nat n Y)
        [rewrite > H6;rewrite > (fv_encode (swap_NTyp X Y n2) (swap X Y Y::l) 
                      (swap_list X Y (Y::l)));
           [rewrite < (encode_swap X Y n2);
              [rewrite < (fv_encode ? (Y::l) (Y::l@[Y]))
                 [rewrite > encode_append;
                    [reflexivity(*rewrite < (fv_encode n2 (Y::l) (Y::l@[Y]));
                       [reflexivity
                       |intros;elim (decidable_eq_nat x Y)
                          [rewrite > H8;simplify;rewrite > eqb_n_n;simplify;
                           split [reflexivity|intro;reflexivity]
                          |simplify;rewrite > (not_eq_to_eqb_false ? ? H8);
                           simplify;elim l
                             [simplify;rewrite > (not_eq_to_eqb_false ? ? H8);
                              simplify;split [reflexivity|intro;destruct H9]
                             |elim H9;simplify;elim (eqb x t)
                                [simplify;split [reflexivity|intro;reflexivity]
                                |simplify;rewrite < H10;generalize in match H11;
                                 elim (lookup x l1)
                                   [split
                                      [reflexivity
                                      |intro;rewrite < (H12 H13);reflexivity]
                                   |split [reflexivity|intro;destruct H13]]]]]]*)
                    |simplify;constructor 1]
                 |intros;simplify;elim (decidable_eq_nat x Y)
                    [rewrite > (eq_to_eqb_true ? ? H8);simplify;split
                       [reflexivity|intro;reflexivity]
                    |rewrite > (not_eq_to_eqb_false ? ? H8);simplify;elim l
                       [simplify;rewrite > (not_eq_to_eqb_false ? ? H8);
                        simplify;split [reflexivity|intro;destruct H9]
                       |simplify;elim (eqb x t)
                          [simplify;split [reflexivity|intro;reflexivity]
                          |simplify;elim H9;split
                             [assumption
                             |intro;rewrite < (H11 H12);reflexivity]]]]]
              |intro;elim (decidable_eq_nat X Y)
                 [rewrite > H8;apply in_list_head
                 |elim H8;apply H5;simplify;apply in_list_to_in_list_append_r;
                  rewrite > H6;apply (in_remove ? ? ? H8 H7)]
              |apply in_list_head]
           |intros;simplify;rewrite > swap_right;rewrite < Hcut;
            split [reflexivity|intro;reflexivity]]
        |(*rewrite < Hcut;*)elim (decidable_eq_nat n X)
           [rewrite > H7;rewrite > (fv_encode (swap_NTyp X Y n2) (swap X Y X::l)
                         (swap_list X Y (X::l)))
              [rewrite > (encode_swap X Y n2);
                 [simplify;
                  cut (swap X Y X::swap_list X Y (l@[Y]) = 
                        (swap X Y X::swap_list X Y l)@[X])
                    [rewrite > Hcut1;cut (S (length ? l) = (length ? (swap X Y X::swap_list X Y l)))
                       [rewrite > Hcut2;rewrite < (encode_subst_simple X 
                              (swap_NTyp X Y n2) (swap X Y X::swap_list X Y l));
                        reflexivity
                       |simplify;elim l
                          [reflexivity
                          |simplify;rewrite < H8;reflexivity]]
                    |simplify;elim l
                       [simplify;rewrite > swap_right;reflexivity
                       |simplify;destruct;rewrite > Hcut1;reflexivity]]
                 |intro;apply in_list_head
                 |apply in_list_cons;elim l
                    [simplify;apply in_list_head
                    |simplify;apply in_list_cons;assumption]]
              |intros;simplify;rewrite < Hcut;
               split [reflexivity|intro;reflexivity]]
           |rewrite > (swap_other X Y n)
              [rewrite < (append_associative ? [n] l [Y]);
               cut (S (length nat l) = length nat (n::l)) [|reflexivity]
               rewrite > Hcut1;rewrite < (H2 n2);
                 [reflexivity
                 |autobatch
                 |intro;apply H7;inversion H8;intros
                    [destruct;reflexivity
                    |destruct;elim (H3 H9)]
                 |intro;apply H6;inversion H8;intros
                    [destruct;reflexivity
                    |destruct;elim (H4 H9)]
                 |intro;apply H5;simplify;apply in_list_to_in_list_append_r;
                  apply (in_remove ? ? ? ? H8);intro;apply H7;symmetry;assumption]
              |*:assumption]]]
     |autobatch
     |intro;apply H5;simplify;apply in_list_to_in_list_append_l;assumption]]
qed.

lemma swap_case: ∀u,v,x.(swap u v x) = u ∨ (swap u v x) = v ∨ (swap u v x = x).
intros.unfold in match swap.simplify.elim (eqb x u)
  [simplify;autobatch
  |simplify;elim (eqb x v);simplify;autobatch]
qed.

lemma in_fvNTyp_in_fvNenv : ∀G,T.(NWFType G T) → (incl ? (fv_NTyp T) (fv_Nenv G)).
intros;elim H
  [simplify;unfold;intros;inversion H2;intros
     [destruct;assumption
     |destruct;elim (not_in_list_nil ? ? H3)]
  |simplify;unfold;intros;elim (not_in_list_nil ? ? H1)
  |simplify;unfold;intros;elim (in_list_append_to_or_in_list ? ? ? ? H5)
     [apply (H2 ? H6)|apply (H4 ? H6)]
  |simplify;unfold;intros;elim (in_list_append_to_or_in_list ? ? ? ? H5)
     [apply H2;assumption
     |elim (fresh_name (x::fv_Nenv l@var_NTyp n2));lapply (H4 a)
        [cut (a ≠ x ∧ x ≠ n)
           [elim Hcut;lapply (Hletin x)
              [simplify in Hletin1;inversion Hletin1;intros;
                 [destruct;elim H8;reflexivity
                 |destruct;assumption]
              |generalize in match H6;generalize in match H7;elim n2
                 [simplify in H11;elim (decidable_eq_nat n n3)
                    [rewrite > (eq_to_eqb_true ? ? H12) in H11;simplify in H11;
                     elim (not_in_list_nil ? ? H11)
                    |rewrite > (not_eq_to_eqb_false ? ? H12) in H11;
                     simplify in H11;inversion H11;intros
                       [destruct;simplify;
                        rewrite > swap_other
                          [apply in_list_head
                          |intro;apply H8;rewrite > H13;reflexivity
                          |intro;apply H9;rewrite > H13;reflexivity]
                       |destruct;elim (not_in_list_nil ? ? H13)]]
                 |simplify in H11;elim (not_in_list_nil ? ? H11)
                 |simplify in H13;simplify;elim (remove_inlist ? ? ? H13);
                  elim (in_list_append_to_or_in_list ? ? ? ? H14)
                    [apply in_list_to_in_list_append_l;apply H10
                       [intro;apply H12;simplify;
                        rewrite < (append_associative ? [x] (fv_Nenv l) (var_NTyp n3 @ var_NTyp n4));
                        elim (in_list_append_to_or_in_list ? ? (x::fv_Nenv l) (var_NTyp n3) H17);
                          [apply in_list_to_in_list_append_l;assumption
                          |apply in_list_to_in_list_append_r;
                           apply in_list_to_in_list_append_l;assumption]
                       |apply (in_remove ? ? ? H15 H16)]
                    |apply in_list_to_in_list_append_r;apply H11
                       [intro;apply H12;simplify;
                        rewrite < (append_associative ? [x] (fv_Nenv l) (var_NTyp n3 @ var_NTyp n4));
                        elim (in_list_append_to_or_in_list ? ? (x::fv_Nenv l) (var_NTyp n4) H17);
                          [apply in_list_to_in_list_append_l;assumption
                          |apply in_list_to_in_list_append_r;
                           apply in_list_to_in_list_append_r;assumption]
                       |apply (in_remove ? ? ? H15 H16)]]
                 |simplify;simplify in H13;elim (remove_inlist ? ? ? H13);
                  elim (nat_in_list_case ? ? ? H14);
                    [apply in_list_to_in_list_append_r;apply in_remove;
                       [elim (remove_inlist ? ? ? H16);intro;apply H18;
                        elim (swap_case a n n3)
                          [elim H20
                             [elim H8;symmetry;rewrite < H21;assumption
                             |elim H9;rewrite < H21;assumption]
                          |rewrite < H20;assumption]
                       |apply H11; 
                          [rewrite < (append_associative ? [x] (fv_Nenv l) (var_NTyp n5));
                           intro;apply H12;simplify;
                           rewrite < (append_associative ? [x] (fv_Nenv l) (n3::var_NTyp n4 @ var_NTyp n5));
                           elim (nat_in_list_case ? ? ? H17)
                             [apply in_list_to_in_list_append_r;
                              apply in_list_cons;
                              apply in_list_to_in_list_append_r;assumption
                             |apply in_list_to_in_list_append_l;assumption]
                          |elim (remove_inlist ? ? ? H16);apply in_remove
                             [assumption
                             |assumption]]]
                    |apply in_list_to_in_list_append_l;apply H10;
                       [rewrite < (append_associative ? [x] (fv_Nenv l) (var_NTyp n4));
                        intro;apply H12;simplify;
                        rewrite < (append_associative ? [x] (fv_Nenv l) (n3::var_NTyp n4@var_NTyp n5));
                        elim (nat_in_list_case ? ? ? H17)
                          [apply in_list_to_in_list_append_r;apply in_list_cons;
                           apply in_list_to_in_list_append_l;assumption
                          |apply in_list_to_in_list_append_l;assumption]
                       |apply in_remove;assumption]]]]
           |split
              [intro;apply H7;rewrite > H8;apply in_list_head
              |elim (remove_inlist ? ? ? H6);assumption]]
        |intro;apply H7;apply in_list_cons;apply in_list_to_in_list_append_l;
         assumption
        |right;intro;apply H7;apply in_list_cons;
         apply in_list_to_in_list_append_r;apply (incl_fv_var ? ? H8)]]]
qed.

lemma fv_NTyp_fv_Typ : ∀T,X,l.(X ∈ (fv_NTyp T)) → ¬(X ∈ l) → 
                          (X ∈ (fv_type (encodetype T l))).
intros 2;elim T
  [simplify;simplify in H;cut (X = n)
     [rewrite < Hcut;generalize in match (lookup_in X l);elim (lookup X l)
        [elim H1;apply H2;reflexivity
        |simplify;apply in_list_head]
     |(*FIXME*)generalize in match H;intro;inversion H;intros;
        [destruct;reflexivity
        |destruct;elim (not_in_list_nil ? ? H3)]]
  |simplify in H;elim (not_in_list_nil ? ? H)
  |simplify;simplify in H2;
   elim (in_list_append_to_or_in_list ? ? ? ? H2);
     [apply in_list_to_in_list_append_l;apply (H ? H4 H3)
     |apply in_list_to_in_list_append_r;apply (H1 ? H4 H3)]
  |simplify;simplify in H2;
   elim (in_list_append_to_or_in_list ? ? ? ? H2)
     [apply in_list_to_in_list_append_l;apply (H ? H4 H3)
     |apply in_list_to_in_list_append_r;
      elim (remove_inlist ? ? ? H4);apply (H1 ? H5);intro;apply H6;
      inversion H7;intros
        [destruct;reflexivity
        |destruct;elim (H3 H8)]]]
qed.

lemma adeq_WFT : ∀G,T.NWFType G T → WFType (encodeenv G) (encodetype T []).
intros;elim H
  [simplify;apply WFT_TFree;rewrite < eq_fv_Nenv_fv_env;assumption
  |simplify;apply WFT_Top;
  |simplify;apply WFT_Arrow;assumption
  |simplify;apply WFT_Forall
     [assumption
     |intros;rewrite < (encode_subst n2 X n []);
        [simplify in H4;apply H4
           [rewrite > (eq_fv_Nenv_fv_env l);assumption
           |elim (decidable_eq_nat X n)
              [left;assumption
              |right;intro;apply H6;apply (fv_NTyp_fv_Typ ? ? ? H8);intro;
               apply H7;inversion H9;intros
                 [destruct;reflexivity
                 |destruct;
                  elim (not_in_list_nil ? ? H10)]]]
        |4:intro;elim (decidable_eq_nat X n)
           [assumption
           |elim H6;cut (¬(X ∈ [n]))
              [generalize in match Hcut;generalize in match [n];
               generalize in match H7;elim n2
                 [simplify in H9;generalize in match H9;intro;inversion H9;intros;
                    [destruct;simplify;
                     generalize in match (lookup_in X l1);elim (lookup X l1)
                       [elim H10;apply H12;reflexivity
                       |simplify;apply in_list_head]
                    |destruct;
                     elim (not_in_list_nil ? ? H12)]
                 |simplify in H9;elim (not_in_list_nil ? ? H9)
                 |simplify;simplify in H11;
                  elim (in_list_append_to_or_in_list ? ? ? ? H11);autobatch
                 |simplify;simplify in H11;
                  elim (in_list_append_to_or_in_list ? ? ? ? H11);
                    [autobatch
                    |elim (remove_inlist ? ? ? H13);
                     apply in_list_to_in_list_append_r;
                     apply (H10 H14);
                     intro;inversion H16;intros;
                       [destruct;elim H15;reflexivity
                       |destruct;elim H12;assumption]]]
              |intro;elim H8;inversion H9;intros
                 [destruct;autobatch
                 |destruct;elim (not_in_list_nil ? ? H10)]]]
        |*:apply not_in_list_nil]]] 
qed.

lemma not_in_list_encodetype : \forall T,l,x.in_list ? x l \to
                      \lnot (in_list ? x (fv_type (encodetype T l))).
intro;elim T;simplify
  [apply (bool_elim ? (lookup n l));intro
     [simplify;apply not_in_list_nil
     |simplify;intro;inversion H2;intros
        [destruct;
         rewrite > (in_lookup ? ? H) in H1;destruct H1
        |destruct;apply (not_in_list_nil ? ? H3)]]
  |apply not_in_list_nil
  |intro;elim (nat_in_list_case ? ? ? H3)
     [apply H1;assumption
     |apply H;assumption]
  |intro;elim (nat_in_list_case ? ? ? H3)
     [apply (H1 (n::l) x ? H4);apply in_list_cons;assumption
     |apply H;assumption]]
qed.

lemma incl_fv_encode_fv : \forall T,l.incl ? (fv_type (encodetype T l)) (fv_NTyp T).
intro;elim T;simplify;unfold;
  [intro;elim (lookup n l)
     [simplify in H;elim (not_in_list_nil ? ? H)
     |simplify in H;assumption]
  |intros;elim (not_in_list_nil ? ? H)
  |intros;elim (in_list_append_to_or_in_list ? ? ? ? H2)
     [apply in_list_to_in_list_append_l;apply H;autobatch
     |apply in_list_to_in_list_append_r;apply H1;autobatch]
  |intros;elim (in_list_append_to_or_in_list ? ? ? ? H2)
     [apply in_list_to_in_list_append_l;apply H;autobatch
     |apply in_list_to_in_list_append_r;apply in_remove
        [intro;apply (not_in_list_encodetype n2 (n::l) x)
           [rewrite > H4;apply in_list_head
           |assumption]
        |apply (H1 (n::l));assumption]]]
qed.

lemma adeq_WFT2 : ∀G1,T1.WFType G1 T1 → 
                     ∀G2,T2.G1 = encodeenv G2 → T1 = encodetype T2 [] → 
                   NWFType G2 T2.
intros 3;elim H
  [rewrite > H2 in H1;rewrite < eq_fv_Nenv_fv_env in H1;
   cut (T2 = TName n) 
     [|generalize in match H3;elim T2
        [simplify in H4;destruct;reflexivity
        |simplify in H4;destruct H4
        |simplify in H6;destruct H6
        |simplify in H6;destruct H6]]
   rewrite > Hcut;apply NWFT_TName;assumption
  |cut (T2 = NTop) 
     [|generalize in match H2;elim T2
        [simplify in H3;destruct H3
        |reflexivity
        |simplify in H5;destruct H5
        |simplify in H5;destruct H5]]
   rewrite > Hcut;apply NWFT_Top;
  |cut (∃U,V.T2 = (NArrow U V)) 
     [|generalize in match H6;elim T2
        [1,2:simplify in H7;destruct H7
        |apply (ex_intro ? ? n);apply (ex_intro ? ? n1);reflexivity
        |simplify in H9;destruct H9]]
   elim Hcut;elim H7;rewrite > H8 in H6;simplify in H6;destruct;
   apply NWFT_Arrow;autobatch
  |cut (\exists Z,U,V.T2 = NForall Z U V) 
     [|generalize in match H6;elim T2
        [1,2:simplify in H7;destruct H7
        |simplify in H9;destruct H9
        |apply (ex_intro ? ? n);apply (ex_intro ? ? n1);
         apply (ex_intro ? ? n2);reflexivity]]
   elim Hcut;elim H7;elim H8;clear Hcut H7 H8;rewrite > H9;
   rewrite > H9 in H6;simplify in H6;destruct;apply NWFT_Forall
     [autobatch
     |intros;elim H6
        [rewrite > H7;cut (swap_NTyp a a a2 = a2) 
           [|elim a2;simplify
              [rewrite > swap_same;reflexivity
              |reflexivity
              |rewrite > H8;rewrite > H9;reflexivity
              |rewrite > swap_same;rewrite > H8;rewrite > H9;reflexivity]]
         rewrite > Hcut;apply (H4 Y)
           [rewrite < eq_fv_Nenv_fv_env;assumption
           |rewrite > H7;apply not_in_list_encodetype;
            apply in_list_head
           |rewrite > H7;simplify;reflexivity
           |rewrite > H7;autobatch]
        |apply (H4 Y)
           [rewrite < eq_fv_Nenv_fv_env;assumption
           |intro;apply H7;apply incl_fv_encode_fv;autobatch
           |simplify;reflexivity
           |symmetry;apply (encode_subst a2 Y a []);
              [3:intro;elim (H7 H8)
              |*:autobatch]]]]]
qed.

lemma adeq_WFE : ∀G.NWFEnv G → WFEnv (encodeenv G).
intros;elim H
  [simplify;apply WFE_Empty
  |simplify;apply WFE_cons;
     [2:rewrite < eq_fv_Nenv_fv_env;]
   autobatch]
qed.

lemma NWFT_env_incl : ∀G,T.NWFType G T → ∀H.incl ? (fv_Nenv G) (fv_Nenv H) 
                      → NWFType H T.
intros 3;elim H
  [apply NWFT_TName;apply (H3 ? H1)
  |apply NWFT_Top
  |apply NWFT_Arrow
     [apply (H2 ? H6)
     |apply (H4 ? H6)]
  |apply NWFT_Forall
     [apply (H2 ? H6)
     |intros;apply (H4 ? ? H8);
        [intro;apply H7;apply (H6 ? H9)
        |unfold;intros;simplify;simplify in H9;inversion H9;intros
           [destruct;apply in_list_head
           |destruct;apply in_list_cons;apply (H6 ? H10)]]]]
qed.

(*lemma NWFT_subst : 
  \forall T,U,a,X,Y,G.
    NWFType (mk_nbound true a U::G) (swap_NTyp a X T) \to
    \lnot (in_list ? a (Y::X::fv_NTyp T@fv_Nenv G)) \to
    \lnot (in_list ? Y (fv_Nenv G)) \to
    (Y = X \lor \lnot (in_list ? Y (fv_NTyp T))) \to
    NWFType (mk_nbound true Y U::G) (swap_NTyp Y X T).
apply NTyp_len_ind;intro;cases U
  [4:simplify;intros;apply NWFT_Forall
     [
     |intros;apply (H ? ? ? Y)
        [2:inversion H1;simplify;intros;destruct;
           [
    
intros 7;elim T
  [4:simplify;apply NWFT_Forall
     [
     |intros;*)


lemma NJSubtype_to_NWFT : ∀G,T,U.NJSubtype G T U → NWFType G T ∧ NWFType G U.
intros;elim H
  [split [assumption|apply NWFT_Top]
  |split;apply NWFT_TName;assumption
  |elim H3;split; 
     [apply NWFT_TName;generalize in match H1;elim l
        [elim (not_in_list_nil ? ? H6)
        |inversion H7;intros
           [rewrite < H8;simplify;apply in_list_head
           |destruct;elim t;simplify;apply in_list_cons;
            apply H6;assumption]]
     |assumption]
  |elim H2;elim H4;split;apply NWFT_Arrow;assumption
  |split;assumption
  |elim H2;split
     [lapply (adeq_WFT ? ? H5);apply (adeq_WFT2 ? ? Hletin);autobatch
     |lapply (adeq_WFT ? ? H6);apply (adeq_WFT2 ? ? Hletin);autobatch]]
qed.

theorem adequacy : ∀G,T,U.NJSubtype G T U → 
                    JSubtype (encodeenv G) (encodetype T []) (encodetype U []).
intros;elim H;simplify
  [1,3,4:autobatch
  |apply SA_Refl_TVar
     [apply (adeq_WFE ? H1)|rewrite < eq_fv_Nenv_fv_env;assumption]
  |apply SA_All
     [assumption
     |intros;lapply (NSA_All ? ? ? ? ? ? ? H1 H2 H3 H5);
      rewrite < (encode_subst n3 X n [])
        [rewrite < (encode_subst n5 X n1 [])
           [rewrite < eq_fv_Nenv_fv_env in H7;
            elim (NJSubtype_to_NWFT ? ? ? Hletin);
            lapply (in_fvNTyp_in_fvNenv ? ? H8);
            lapply (in_fvNTyp_in_fvNenv ? ? H9);
            simplify in Hletin1;simplify in Hletin2;
            apply (H6 ? H7)
              [elim (decidable_eq_nat X n)
                 [left;assumption
                 |right;intro;lapply (in_remove ? ? ? H10 H11);elim H7;
                  apply Hletin1;apply in_list_to_in_list_append_r;assumption]
              |elim (decidable_eq_nat X n1)
                 [left;assumption
                 |right;intro;lapply (in_remove ? ? ? H10 H11);elim H7;
                  apply Hletin2;apply in_list_to_in_list_append_r;assumption]]
           |2,3:apply not_in_list_nil
           |intro;elim (NJSubtype_to_NWFT ? ? ? Hletin);
            lapply (in_fvNTyp_in_fvNenv ? ? H10);simplify in Hletin1;
            elim (decidable_eq_nat X n1)
              [assumption
              |lapply (in_remove ? ? ? H11 H8);elim H7;rewrite < eq_fv_Nenv_fv_env;
               apply Hletin1;apply in_list_to_in_list_append_r;assumption]]
        |2,3:apply not_in_list_nil
        |intro;elim (NJSubtype_to_NWFT ? ? ? Hletin);lapply (in_fvNTyp_in_fvNenv ? ? H9);
         simplify in Hletin1;elim (decidable_eq_nat X n)
           [assumption
           |lapply (in_remove ? ? ? H11 H8);elim H7;rewrite < eq_fv_Nenv_fv_env;
            apply Hletin1;apply in_list_to_in_list_append_r;assumption]]]
  |rewrite < (alpha_to_encode ? ? H3);rewrite < (alpha_to_encode ? ? H4);
   assumption]
qed.

let rec closed_type T n ≝
  match T with
    [ TVar m ⇒ m < n 
    | TFree X ⇒ True
    | Top ⇒ True
    | Arrow T1 T2 ⇒ closed_type T1 n ∧ closed_type T2 n
    | Forall T1 T2 ⇒  closed_type T1 n ∧ closed_type T2 (S n)].
    
alias id "nth" = "cic:/matita/list/list/nth.con".
alias id "length" = "cic:/matita/list/list/length.con".
definition distinct_list ≝
λl.∀n,m.n < length ? l → m < length ? l → n ≠ m → nth ? l O n ≠ nth ? l O m.

lemma posn_nth: ∀l,n.distinct_list l → n < length ? l → 
                    posn l (nth ? l O n) = n.
intro;elim l
  [simplify in H1;elim (not_le_Sn_O ? H1)
  |simplify in H2;generalize in match H2;elim n
     [simplify;rewrite > eqb_n_n;simplify;reflexivity
     |simplify;cut (nth ? (t::l1) O (S n1) ≠ nth ? (t::l1) O O)
        [simplify in Hcut;rewrite > (not_eq_to_eqb_false ? ? Hcut);simplify;
         rewrite > (H n1)
           [reflexivity
           |unfold;intros;unfold in H1;lapply (H1 (S n2) (S m));
              [simplify in Hletin;assumption
              |2,3:simplify;autobatch
              |intro;apply H7;destruct H8;reflexivity]
           |autobatch]
        |intro;apply H1;
           [6:apply H5
           |skip
           |skip
           |*:autobatch]]]]
qed.

lemma nth_in_list : ∀l,n. n < length ? l → nth ? l O n ∈ l.
intro;elim l
  [simplify in H;elim (not_le_Sn_O ? H)
  |generalize in match H1;elim n
     [simplify;apply in_list_head
     |simplify;apply in_list_cons;apply H;simplify in H3;apply (le_S_S_to_le ? ? H3)]]
qed.

lemma lookup_nth : \forall l,n.n < length ? l \to 
                   lookup (nth nat l O n) l = true.
intro;elim l
  [elim (not_le_Sn_O ? H);
  |generalize in match H1;elim n
     [simplify;rewrite > eqb_n_n;reflexivity
     |simplify;elim (eqb (nth nat l1 O n1) t)
        [reflexivity
        |simplify;apply H;apply le_S_S_to_le;assumption]]]
qed.
    
lemma decoder : ∀T,n.closed_type T n → 
                     ∀l.length ? l = n → distinct_list l →
                  (\forall x. in_list ? x (fv_type T) \to \lnot in_list ? x l) \to   
                     ∃U.T = encodetype U l.
intro;elim T
  [simplify in H;apply (ex_intro ? ? (TName (nth ? l O n)));simplify;
   rewrite > lookup_nth
     [simplify;rewrite > posn_nth;
        [reflexivity|assumption|rewrite > H1;assumption]
     |rewrite > H1;assumption]
  |apply (ex_intro ? ? (TName n));rewrite > (fv_encode (TName n) l []);
     [simplify;reflexivity
     |intros;simplify in H3;simplify in H4;lapply (H3 ? H4);
      cut (lookup x l = false)
        [rewrite > Hcut;simplify;split
           [reflexivity|intro;destruct H5]
        |elim (bool_to_decidable_eq (lookup x l) true)
           [lapply (lookup_in ? ? H5);elim (Hletin Hletin1)
           |generalize in match H5;elim (lookup x l);
              [elim H6;reflexivity|reflexivity]]]]
  |apply (ex_intro ? ? NTop);simplify;reflexivity
  |simplify in H2;elim H2;lapply (H ? H6 ? H3 H4);
     [lapply (H1 ? H7 ? H3 H4)
        [elim Hletin;elim Hletin1;
         apply (ex_intro ? ? (NArrow a a1));simplify;
         rewrite < H9;rewrite < H8;reflexivity
        |intros;apply H5;simplify;apply in_list_to_in_list_append_r;assumption]
     |intros;apply H5;simplify;apply in_list_to_in_list_append_l;assumption]
  |simplify in H2;elim H2;elim (H ? H6 ? H3 H4);elim (fresh_name (fv_type t1@l));
     [elim (H1 ? H7 (a1::l))
        [apply (ex_intro ? ? (NForall a1 a a2));simplify;rewrite < H8;rewrite < H10;
         reflexivity
        |simplify;rewrite > H3;reflexivity
        |unfold;intros;intro;apply H12;generalize in match H13;generalize in match H10;
         generalize in match H11;generalize in match H9;
         generalize in match m;generalize in match n1;
         apply nat_elim2
           [intro;elim n2
              [reflexivity
              |simplify in H18;rewrite > H18 in H9;elim H9;simplify in H16;
               lapply (le_S_S_to_le ? ? H16);apply in_list_to_in_list_append_r;
               autobatch]
           |intro;intros;change in H17:(? ? % ?) with (nth nat l O n2);
            simplify in H17:(? ? ? %);elim H9;rewrite < H17;
            apply in_list_to_in_list_append_r;apply nth_in_list;
            simplify in H16;apply (le_S_S_to_le ? ? H16)
           |intros;change in H18 with (nth nat l O n2 = nth nat l O m1);
            unfold in H4;elim (decidable_eq_nat n2 m1)
              [rewrite > H19;reflexivity
              |simplify in H17;simplify in H16;elim (H4 ? ? ? ? H19)
                 [assumption
                 |apply (le_S_S_to_le ? ? H17)
                 |apply (le_S_S_to_le ? ? H16)]]]
        |intro;elim (in_list_cons_case ? ? ? ? H11)
           [apply H9;apply in_list_to_in_list_append_l;rewrite < H12;assumption
           |apply (H5 x)
              [simplify;apply in_list_to_in_list_append_r;assumption
              |assumption]]]
     |apply H5;simplify;apply in_list_to_in_list_append_l;assumption]]
qed.

lemma closed_subst : \forall T,X,n.closed_type (subst_type_nat T (TFree X) n) n 
                     \to closed_type T (S n).
intros 2;elim T 0;simplify;intros
  [elim (decidable_eq_nat n n1)
     [rewrite > H1;apply le_n
     |rewrite > (not_eq_to_eqb_false ? ? H1) in H;simplify in H;
      apply le_S;assumption]
  |2,3:apply I
  |elim H2;split;autobatch
  |elim H2;split;autobatch]
qed.

lemma WFT_to_closed: ∀G,T.WFType G T → closed_type T O.
intros;elim H;simplify
  [apply I
  |apply I
  |split;assumption
  |split
     [assumption
     |elim (fresh_name (fv_env l@fv_type t1));lapply (H4 a)
        [autobatch
        |intro;apply H5;apply in_list_to_in_list_append_l;assumption
        |intro;apply H5;apply in_list_to_in_list_append_r;assumption]]]
qed.

lemma adeq_WFE2 : ∀G1.WFEnv G1 → ∀G2.(G1 = encodeenv G2) → NWFEnv G2.
intros 2;elim H 0
  [intro;elim G2
     [apply NWFE_Empty
     |simplify in H2;destruct H2]
  |intros 9;elim G2
     [simplify in H5;destruct H5
     |generalize in match H6;elim t1;simplify in H7;destruct H7;apply NWFE_cons
        [apply H2;reflexivity
        |rewrite > eq_fv_Nenv_fv_env;assumption
        |autobatch]]]
qed.

lemma xxx : \forall b,X,T,l.
            in_list ? (mk_bound b X (encodetype T [])) (encodeenv l) \to
            \exists U.encodetype U [] = encodetype T [] \land
                      in_list ? (mk_nbound b X U) l.
intros 4;elim l
  [simplify in H;elim (not_in_list_nil ? ? H)
  |simplify in H1;inversion H1;elim t 0;simplify;intros;destruct;
     [apply (ex_intro ? ? n1);split;autobatch
     |elim (H H2);elim H4;apply (ex_intro ? ? a);split;autobatch]]
qed.

lemma eq_swap_NTyp_to_case :
  \forall X,Y,Z,T.\lnot in_list ? Y (X::var_NTyp T) \to
    swap_NTyp Z Y (swap_NTyp Y X T) = swap_NTyp Z X T \to
      Z = X \lor \lnot in_list ? Z (fv_NTyp T).
intros 4;elim T
  [simplify in H;simplify in H1;elim (decidable_eq_nat X n)
     [rewrite > H2;simplify;elim (decidable_eq_nat Z n)
        [left;assumption
        |right;intro;apply H3;apply in_list_singleton_to_eq;assumption]
     |elim (decidable_eq_nat Y n)
        [elim H;rewrite > H3;apply in_list_cons;apply in_list_head
        |rewrite > (swap_other Y X n) in H1
           [elim (decidable_eq_nat Z n)
              [rewrite > H4 in H1;do 2 rewrite > swap_left in H1;
               destruct H1;elim H;apply in_list_head
              |elim (decidable_eq_nat Z X)
                 [left;assumption
                 |rewrite > (swap_other Z X n) in H1
                    [right;intro;apply H3;simplify in H6;
                     rewrite > (in_list_singleton_to_eq ? ? ? H6) in H1;
                     rewrite > swap_left in H1;destruct H1;reflexivity
                    |intro;apply H4;symmetry;assumption
                    |intro;apply H2;symmetry;assumption]]]
           |intro;apply H3;symmetry;assumption
           |intro;apply H2;symmetry;assumption]]]
  |simplify;right;apply not_in_list_nil
  |elim H
     [left;assumption
     |elim H1
        [left;assumption
        |right;simplify;intro;elim (in_list_append_to_or_in_list ? ? ? ? H6)
           [elim (H4 H7)
           |elim (H5 H7)]
        |intro;apply H2;simplify;inversion H5;intros;destruct;
           [apply in_list_head
           |apply in_list_cons;apply in_list_to_in_list_append_r;assumption]
        |simplify in H3;destruct H3;assumption]
     |intro;apply H2;simplify;inversion H4;intros;destruct;
        [apply in_list_head
        |apply in_list_cons;apply in_list_to_in_list_append_l;assumption]
     |simplify in H3;destruct H3;assumption]
  |elim H
     [left;assumption
     |elim H1
        [left;assumption
        |right;simplify;intro;elim (in_list_append_to_or_in_list ? ? ? ? H6)
           [elim (H4 H7)
           |elim H5;elim (remove_inlist ? ? ? H7);assumption]
        |intro;apply H2;simplify;inversion H5;intros;destruct;
           [apply in_list_head
           |do 2 apply in_list_cons;apply in_list_to_in_list_append_r;assumption]
        |simplify in H3;destruct H3;assumption]
     |intro;apply H2;simplify;inversion H4;intros;destruct;
        [apply in_list_head
        |do 2 apply in_list_cons;apply in_list_to_in_list_append_l;assumption]
     |simplify in H3;destruct H3;assumption]]
qed.


theorem faithfulness : ∀G1,T1,U1.G1 ⊢ T1 ⊴ U1 → 
                          ∀G2,T2,U2.
                       G1 = encodeenv G2 →
                       T1 = encodetype T2 [] →
                       U1 = encodetype U2 [] →
                       NJSubtype G2 T2 U2.
intros 4;elim H 0
  [intros;cut (U2 = NTop) 
     [|generalize in match H5;elim U2 0;simplify;intros;destruct;reflexivity]
  rewrite > Hcut;apply NSA_Top;
     [apply (adeq_WFE2 ? H1);assumption
     |apply (adeq_WFT2 ? ? H2);assumption]
  |intros;cut (T2 = TName n ∧ U2 = TName n) 
   [|split
     [generalize in match H4;elim T2 0;simplify;intros;destruct;reflexivity
     |generalize in match H5;elim U2 0;simplify;intros;destruct;reflexivity]]
   elim Hcut;
   rewrite > H6;rewrite > H7;apply NSA_Refl_TVar; 
     [apply (adeq_WFE2 ? H1);assumption
     |rewrite > H3 in H2;rewrite < eq_fv_Nenv_fv_env in H2;assumption]
  |intros;cut (T2 = TName n) 
     [|generalize in match H5;elim T2 0;simplify;intros;destruct;reflexivity]
   rewrite > Hcut;
   elim (decoder t1 O ? []);
     [rewrite > H4 in H1;rewrite > H7 in H1;elim (xxx ? ? ? ? H1);elim H8;
      apply NSA_Trans_TVar
        [apply a1
        |assumption
        |apply H3;autobatch]
     |apply (WFT_to_closed l);apply (JS_to_WFT1 ? ? ? H2)
     |simplify;reflexivity
     |unfold;intros;simplify in H7;elim (not_le_Sn_O ? H7)
     |apply not_in_list_nil]
  |intros;cut (∃u,u1,u2,u3.T2 = NArrow u u1 ∧ U2 = NArrow u2 u3)
     [elim Hcut;elim H8;elim H9;elim H10;elim H11;clear Hcut H8 H9 H10 H11;
      rewrite > H12;rewrite > H13;rewrite > H13 in H7;simplify in H7;destruct;
      simplify in H6;destruct;apply NSA_Arrow
        [apply H2;reflexivity
        |apply H4;reflexivity]
     |generalize in match H6;elim T2 0;simplify;intros;destruct;
      generalize in match H7;elim U2 0;simplify;intros;destruct;
      autobatch depth=6 width=2 size=7]
  |intros;cut (∃n,u,u1,n1,u2,u3.T2 = NForall n u u1 ∧ U2 = NForall n1 u2 u3)
     [elim Hcut;elim H8;elim H9;elim H10;elim H11;elim H12;elim H13;
      clear Hcut H8 H9 H10 H11 H12 H13;rewrite > H14;rewrite > H15;
      rewrite > H14 in H6;rewrite > H15 in H7;simplify in H6;simplify in H7;
      destruct H6;destruct H7;lapply (SA_All ? ? ? ? ? H1 H3);destruct H5;
      lapply (JS_to_WFT1 ? ? ? Hletin);lapply (JS_to_WFT2 ? ? ? Hletin);
      apply NSA_All
        [apply (adeq_WFT2 ? ? Hletin1);reflexivity
        |apply (adeq_WFT2 ? ? Hletin2);reflexivity
        |apply H2;reflexivity
        |intros;apply H4;
           [apply Z
           |rewrite < eq_fv_Nenv_fv_env;assumption
           |simplify;reflexivity
           |rewrite < (encode_subst a2 Z a []);
              [reflexivity
              |2,3:apply not_in_list_nil
              |lapply (SA_All ? ? ? ? ? H1 H3);lapply (JS_to_WFT1 ? ? ? Hletin);
               intro;elim (decidable_eq_nat Z a)
                 [assumption
                 |lapply (fv_WFT ? Z ? Hletin1)
                    [elim H5;rewrite > eq_fv_Nenv_fv_env;assumption
                    |simplify;apply in_list_to_in_list_append_r;
                     apply fv_NTyp_fv_Typ
                       [assumption
                       |intro;apply H9;autobatch]]]]
           |rewrite < (encode_subst a5 Z a3 [])
              [reflexivity
              |2,3:apply not_in_list_nil
              |intro;elim H7
                 [assumption
                 |elim (H9 H8)]]]]
     |generalize in match H6;elim T2 0;simplify;intros;destruct;
      generalize in match H7;elim U2 0;simplify;intros;destruct;
      autobatch depth=8 width=2 size=9]]
qed.

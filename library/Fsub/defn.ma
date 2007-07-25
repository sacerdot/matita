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

set "baseuri" "cic:/matita/Fsub/defn".
include "logic/equality.ma".
include "nat/nat.ma".
include "datatypes/bool.ma".
include "nat/compare.ma".
include "list/list.ma".
include "Fsub/util.ma".

(*** representation of Fsub types ***)  
inductive Typ : Set \def
  | TVar : nat \to Typ            (* type var *)
  | TFree: nat \to Typ            (* free type name *)
  | Top : Typ                     (* maximum type *)
  | Arrow : Typ \to Typ \to Typ   (* functions *) 
  | Forall : Typ \to Typ \to Typ. (* universal type *)
  
(*** representation of Fsub terms ***)
inductive Term : Set \def
  | Var : nat \to Term            (* variable *)
  | Free : nat \to Term          (* free name *)
  | Abs : Typ \to Term \to Term   (* abstraction *)
  | App : Term \to Term \to Term  (* function application *)
  | TAbs : Typ \to Term \to Term  (* type abstraction *)
  | TApp : Term \to Typ \to Term. (* type application *)
  
(* representation of bounds *)

record bound : Set \def { 
                          istype : bool;    (* is subtyping bound? *)
                          name   : nat ;    (* name *)
                          btype  : Typ      (* type to which the name is bound *)
                        }.
               
(* representation of Fsub typing environments *)
definition Env \def (list bound).
definition Empty \def (nil bound).
definition Cons \def \lambda G,X,T.((mk_bound false X T) :: G).
definition TCons \def \lambda G,X,T.((mk_bound true X T) :: G).

definition env_append : Env \to Env \to Env \def \lambda G,H.(H @ G).
  
(* notation "hvbox(\Forall S. break T)" 
  non associative with precedence 90
for @{ 'forall $S $T}.

notation "hvbox(#x)"
  with precedence 60
  for @{'var $x}.
  
notation "hvbox(##x)"
  with precedence 61
  for @{'tvar $x}.

notation "hvbox(!x)"
  with precedence 60
  for @{'name $x}.
  
notation "hvbox(!!x)"
  with precedence 61
  for @{'tname $x}.

notation "hvbox(s break \mapsto t)"
  right associative with precedence 55
  for @{ 'arrow $s $t }.

interpretation "universal type" 'forall S T = (cic:/matita/Fsub/defn/Typ.ind#xpointer(1/1/5) S T).

interpretation "bound var" 'var x = (cic:/matita/Fsub/defn/Typ.ind#xpointer(1/1/1) x).

interpretation "bound tvar" 'tvar x = (cic:/matita/Fsub/defn/Typ.ind#xpointer(1/1/3) x).

interpretation "bound tname" 'tname x = (cic:/matita/Fsub/defn/Typ.ind#xpointer(1/1/2) x).

interpretation "arrow type" 'arrow S T = (cic:/matita/Fsub/defn/Typ.ind#xpointer(1/1/4) S T). *) 

(*** Various kinds of substitution, not all will be used probably ***)

(* substitutes i-th dangling index in type T with type U *)
let rec subst_type_nat T U i \def
    match T with
    [ (TVar n) \Rightarrow match (eqb n i) with
      [ true \Rightarrow U
      | false \Rightarrow T]
    | (TFree X) \Rightarrow T
    | Top \Rightarrow T
    | (Arrow T1 T2) \Rightarrow (Arrow (subst_type_nat T1 U i) (subst_type_nat T2 U i))
    | (Forall T1 T2) \Rightarrow (Forall (subst_type_nat T1 U i) (subst_type_nat T2 U (S i))) ].

(* substitutes 0-th dangling index in type T with type U *)
let rec subst_type_O T U  \def subst_type_nat T U O. 

(* substitutes 0-th dangling index in term t with term u *)
let rec subst_term_O t u  \def
  let rec aux t0 i \def
    match t0 with
    [ (Var n) \Rightarrow match (eqb n i) with
      [ true \Rightarrow u
      | false \Rightarrow t0]
    | (Free X) \Rightarrow t0
    | (Abs T1 t1) \Rightarrow (Abs T1 (aux t1 (S i)))
    | (App t1 t2) \Rightarrow (App (aux t1 i) (aux t2 i))
    | (TAbs T1 t1) \Rightarrow (TAbs T1 (aux t1 (S i)))
    | (TApp t1 T1) \Rightarrow (TApp (aux t1 i) T1) ]
  in aux t O.

(* substitutes 0-th dangling index in term T, which shall be a TVar,
   with type U *)
let rec subst_term_tO t T  \def
  let rec aux t0 i \def
    match t0 with
    [ (Var n) \Rightarrow t0 
    | (Free X) \Rightarrow t0
    | (Abs T1 t1) \Rightarrow (Abs (subst_type_nat T1 T i) (aux t1 (S i)))
    | (App t1 t2) \Rightarrow (App (aux t1 i) (aux t2 i))
    | (TAbs T1 t1) \Rightarrow (TAbs (subst_type_nat T1 T i) (aux t1 (S i)))
    | (TApp t1 T1) \Rightarrow (TApp (aux t1 i) (subst_type_nat T1 T i)) ]
  in aux t O.

(* substitutes (TFree X) in type T with type U *)
let rec subst_type_tfree_type T X U on T \def
  match T with
    [ (TVar n) \Rightarrow T
    | (TFree Y) \Rightarrow match (eqb X Y) with
      [ true \Rightarrow U
      | false \Rightarrow T ]
    | Top \Rightarrow T
    | (Arrow T1 T2) \Rightarrow (Arrow (subst_type_tfree_type T1 X U) 
                                       (subst_type_tfree_type T2 X U))
    | (Forall T1 T2) \Rightarrow (Forall (subst_type_tfree_type T1 X U) 
                                       (subst_type_tfree_type T2 X U)) ].
            
(*** height of T's syntactic tree ***)

let rec t_len T \def
  match T with
     [(TVar n) \Rightarrow (S O)
     |(TFree X) \Rightarrow (S O)
     |Top \Rightarrow (S O)
     |(Arrow T1 T2) \Rightarrow (S (max (t_len T1) (t_len T2)))
     |(Forall T1 T2) \Rightarrow (S (max (t_len T1) (t_len T2)))].

definition head \def
  \lambda G:(list bound).match G with
    [ nil \Rightarrow (mk_bound false O Top)
    | (cons b H) \Rightarrow b].

definition head_nat \def
  \lambda G:(list nat).match G with
    [ nil \Rightarrow O
    | (cons n H) \Rightarrow n].

(*** definitions about lists ***)

(* var binding is in env judgement *)                
definition var_bind_in_env : bound \to Env \to Prop \def
  \lambda b,G.(in_list bound b G).

definition fv_env : (list bound) \to (list nat) \def
  \lambda G.(map ? ? (\lambda b.match b with
      [(mk_bound B X T) \Rightarrow X]) G).

(* variable is in env judgement *)              
definition var_in_env : nat \to Env \to Prop \def
  \lambda x,G.(in_list nat x (fv_env G)).
  
definition var_type_in_env : nat \to Env \to Prop \def
  \lambda x,G.\exists T.(var_bind_in_env (mk_bound true x T) G).

let rec fv_type T \def
  match T with
    [(TVar n) \Rightarrow []
    |(TFree x) \Rightarrow [x]
    |Top \Rightarrow []
    |(Arrow U V) \Rightarrow ((fv_type U) @ (fv_type V))
    |(Forall U V) \Rightarrow ((fv_type U) @ (fv_type V))].

(*** Type Well-Formedness judgement ***)

inductive WFType : Env \to Typ \to Prop \def
  | WFT_TFree : \forall X,G.(in_list ? X (fv_env G)) 
                \to (WFType G (TFree X))
  | WFT_Top : \forall G.(WFType G Top)
  | WFT_Arrow : \forall G,T,U.(WFType G T) \to (WFType G U) \to 
                (WFType G (Arrow T U))
  | WFT_Forall : \forall G,T,U.(WFType G T) \to
                 (\forall X:nat.
                    (\lnot (in_list ? X (fv_env G))) \to
                    (\lnot (in_list ? X (fv_type U))) \to
                    (WFType ((mk_bound true X T) :: G) 
                       (subst_type_O U (TFree X)))) \to 
                 (WFType G (Forall T U)).

(*** Environment Well-Formedness judgement ***)

inductive WFEnv : Env \to Prop \def
  | WFE_Empty : (WFEnv Empty)
  | WFE_cons : \forall B,X,T,G.(WFEnv G) \to 
               \lnot (in_list ? X (fv_env G)) \to
                  (WFType G T) \to (WFEnv ((mk_bound B X T) :: G)).
            
(*** Subtyping judgement ***)              
inductive JSubtype : Env \to Typ \to Typ \to Prop \def
  | SA_Top : \forall G:Env.\forall T:Typ.(WFEnv G) \to
             (WFType G T) \to (JSubtype G T Top)
  | SA_Refl_TVar : \forall G:Env.\forall X:nat.(WFEnv G) \to (var_in_env X G) 
                   \to (JSubtype G (TFree X) (TFree X))
  | SA_Trans_TVar : \forall G:Env.\forall X:nat.\forall T:Typ.
                    \forall U:Typ.
                    (var_bind_in_env (mk_bound true X U) G) \to
                    (JSubtype G U T) \to (JSubtype G (TFree X) T)
  | SA_Arrow : \forall G:Env.\forall S1,S2,T1,T2:Typ.
               (JSubtype G T1 S1) \to (JSubtype G S2 T2) \to
               (JSubtype G (Arrow S1 S2) (Arrow T1 T2))
  | SA_All : \forall G:Env.\forall S1,S2,T1,T2:Typ.
             (JSubtype G T1 S1) \to
             (\forall X:nat.\lnot (var_in_env X G) \to
                (JSubtype ((mk_bound true X T1) :: G) 
                   (subst_type_O S2 (TFree X)) (subst_type_O T2 (TFree X)))) \to
             (JSubtype G (Forall S1 S2) (Forall T1 T2)).

(*
notation < "hvbox(e break ⊢ ta \nbsp 'V' \nbsp tb (= \above \alpha))" 
  non associative with precedence 30 for @{ 'subjudg $e $ta $tb }.
notation > "hvbox(e break ⊢ ta 'Fall' break tb)" 
  non associative with precedence 30 for @{ 'subjudg $e $ta $tb }.
notation "hvbox(e break ⊢ ta \lessdot break tb)" 
  non associative with precedence 30 for @{ 'subjudg $e $ta $tb }.  
interpretation "Fsub subtype judgement" 'subjudg e ta tb =
 (cic:/matita/Fsub/defn/JSubtype.ind#xpointer(1/1) e ta tb).

lemma xx : \forall e,ta,tb. e \vdash  ta Fall tb.
*)

(*** Typing judgement ***)
inductive JType : Env \to Term \to Typ \to Prop \def
  | T_Var : \forall G:Env.\forall x:nat.\forall T:Typ.
            (WFEnv G) \to (var_bind_in_env (mk_bound false x T) G) \to
            (JType G (Free x) T)
  | T_Abs : \forall G.\forall T1,T2:Typ.\forall t2:Term.
            \forall x:nat.
            (JType ((mk_bound false x T1)::G) (subst_term_O t2 (Free x)) T2) \to
            (JType G (Abs T1 t2) (Arrow T1 T2))
  | T_App : \forall G.\forall t1,t2:Term.\forall T2:Typ.
            \forall T1:Typ.(JType G t1 (Arrow T1 T2)) \to (JType G t2 T1) \to
            (JType G (App t1 t2) T2)
  | T_TAbs : \forall G:Env.\forall T1,T2:Typ.\forall t2:Term.
             \forall X:nat.
             (JType ((mk_bound true X T1)::G) 
             (subst_term_tO t2 (TFree X)) (subst_type_O T2 (TFree X)))
             \to (JType G (TAbs T1 t2) (Forall T1 T2))
  | T_TApp : \forall G:Env.\forall t1:Term.\forall T2,T12:Typ.
             \forall X:nat.\forall T11:Typ.
             (JType G t1 (Forall T11 (subst_type_tfree_type T12 X (TVar O)))) \to 
             (JSubtype G T2 T11)
             \to (JType G (TApp t1 T2) (subst_type_tfree_type T12 X T2))
  | T_Sub : \forall G:Env.\forall t:Term.\forall T:Typ.
            \forall S:Typ.(JType G t S) \to (JSubtype G S T) \to (JType G t T).

(****** PROOFS ********)

lemma subst_O_nat : \forall T,U.((subst_type_O T U) = (subst_type_nat T U O)).
intros;elim T;simplify;reflexivity;
qed.

(*** theorems about lists ***)

(* FIXME: these definitions shouldn't be part of the poplmark challenge
   - use destruct instead, when hopefully it will get fixed... *) 

lemma inj_head : \forall h1,h2:bound.\forall t1,t2:Env.
                 ((h1::t1) = (h2::t2)) \to (h1 = h2).
intros.
lapply (eq_f ? ? head ? ? H).simplify in Hletin.assumption.
qed.

lemma inj_head_nat : \forall h1,h2:nat.\forall t1,t2:(list nat).
                 ((h1::t1) = (h2::t2)) \to (h1 = h2).
intros.
lapply (eq_f ? ? head_nat ? ? H).simplify in Hletin.assumption.
qed.

lemma inj_tail : \forall A.\forall h1,h2:A.\forall t1,t2:(list A).
                 ((h1::t1) = (h2::t2)) \to (t1 = t2).
intros.lapply (eq_f ? ? (tail ?) ? ? H).simplify in Hletin.assumption.
qed.

(* end of fixme *) 

lemma boundinenv_natinfv : \forall x,G.
                              (\exists B,T.(in_list ? (mk_bound B x T) G)) \to
                              (in_list ? x (fv_env G)).
intros 2;elim G
  [elim H;elim H1;lapply (in_list_nil ? ? H2);elim Hletin
  |elim H1;elim H2;inversion H3
     [intros;rewrite < H4;simplify;apply in_Base
     |intros;elim a3;simplify;apply in_Skip;
      lapply (inj_tail ? ? ? ? ? H7);rewrite > Hletin in H;apply H;
      apply ex_intro
        [apply a
        |apply ex_intro
           [apply a1
           |rewrite > H6;assumption]]]]
qed.

lemma nat_in_list_case : \forall G,H,n.(in_list nat n (H @ G)) \to 
                               (in_list nat n G) \lor (in_list nat n H).
intros 3.elim H
  [simplify in H1;left;assumption
  |simplify in H2;inversion H2
    [intros;lapply (inj_head_nat ? ? ? ? H4);rewrite > Hletin;
     right;apply in_Base
    |intros;lapply (inj_tail ? ? ? ? ? H6);rewrite < Hletin in H3;
     rewrite > H5 in H1;lapply (H1 H3);elim Hletin1
       [left;assumption|right;apply in_Skip;assumption]]]
qed.

lemma natinG_or_inH_to_natinGH : \forall G,H,n.
                      (in_list nat n G) \lor (in_list nat n H) \to
                      (in_list nat n (H @ G)).
intros.elim H1
  [elim H
     [simplify;assumption
     |simplify;apply in_Skip;assumption]
  |generalize in match H2;elim H2
     [simplify;apply in_Base
     |lapply (H4 H3);simplify;apply in_Skip;assumption]]
qed.

lemma natinfv_boundinenv : \forall x,G.(in_list ? x (fv_env G)) \to
                              \exists B,T.(in_list ? (mk_bound B x T) G).
intros 2;elim G 0
  [simplify;intro;lapply (in_list_nil ? ? H);elim Hletin
  |intros 3;elim t;simplify in H1;inversion H1
     [intros;rewrite < H2;simplify;apply ex_intro
        [apply b
        |apply ex_intro
           [apply t1
           |lapply (inj_head_nat ? ? ? ? H3);rewrite > H2;rewrite < Hletin;
            apply in_Base]]
     |intros;lapply (inj_tail ? ? ? ? ? H5);rewrite < Hletin in H2;
      rewrite < H4 in H2;lapply (H H2);elim Hletin1;elim H6;apply ex_intro
        [apply a2
        |apply ex_intro
           [apply a3
           |apply in_Skip;rewrite < H4;assumption]]]]
qed.

theorem varinT_varinT_subst : \forall X,Y,T.
        (in_list ? X (fv_type T)) \to \forall n.
        (in_list ? X (fv_type (subst_type_nat T (TFree Y) n))).
intros 3;elim T
  [simplify in H;elim (in_list_nil ? ? H)
  |simplify in H;simplify;assumption
  |simplify in H;elim (in_list_nil ? ? H)
  |simplify in H2;simplify;elim (nat_in_list_case ? ? ? H2);
   apply natinG_or_inH_to_natinGH;
     [left;apply (H1 H3)
     |right;apply (H H3)]
  |simplify in H2;simplify;elim (nat_in_list_case ? ? ? H2);
   apply natinG_or_inH_to_natinGH;
     [left;apply (H1 H3);
     |right;apply (H H3)]]
qed.

lemma incl_bound_fv : \forall l1,l2.(incl ? l1 l2) \to 
                         (incl ? (fv_env l1) (fv_env l2)).
intros.unfold in H.unfold.intros.apply boundinenv_natinfv.
lapply (natinfv_boundinenv ? ? H1).elim Hletin.elim H2.apply ex_intro
  [apply a
  |apply ex_intro
     [apply a1
     |apply (H ? H3)]]
qed.

lemma incl_nat_cons : \forall x,l1,l2.
                  (incl nat l1 l2) \to (incl nat (x :: l1) (x :: l2)).
intros.unfold in H.unfold.intros.inversion H1
  [intros;lapply (inj_head_nat ? ? ? ? H3);rewrite > Hletin;apply in_Base
  |intros;apply in_Skip;apply H;lapply (inj_tail ? ? ? ? ? H5);rewrite > Hletin;
   assumption]
qed.

lemma WFT_env_incl : \forall G,T.(WFType G T) \to
                     \forall H.(incl ? (fv_env G) (fv_env H)) \to (WFType H T).
intros 3.elim H
  [apply WFT_TFree;unfold in H3;apply (H3 ? H1)
  |apply WFT_Top
  |apply WFT_Arrow [apply (H2 ? H6)|apply (H4 ? H6)]
  |apply WFT_Forall 
     [apply (H2 ? H6)
     |intros;apply H4
        [unfold;intro;apply H7;apply(H6 ? H9)
        |assumption
        |simplify;apply (incl_nat_cons ? ? ? H6)]]]
qed.

lemma fv_env_extends : \forall H,x,B,C,T,U,G.
                          (fv_env (H @ ((mk_bound B x T) :: G))) = 
                          (fv_env (H @ ((mk_bound C x U) :: G))).
intros;elim H
  [simplify;reflexivity
  |elim t;simplify;rewrite > H1;reflexivity]
qed.

lemma lookup_env_extends : \forall G,H,B,C,D,T,U,V,x,y.
            (in_list ? (mk_bound D y V) (H @ ((mk_bound C x U) :: G))) \to
            (y \neq x) \to
            (in_list ? (mk_bound D y V) (H @ ((mk_bound B x T) :: G))).
intros 10;elim H
  [simplify in H1;(*FIXME*)generalize in match H1;intro;inversion H1
     [intros;lapply (inj_head ? ? ? ? H5);rewrite < H4 in Hletin;
      destruct Hletin;absurd (y = x) [symmetry;assumption|assumption]
     |intros;simplify;lapply (inj_tail ? ? ? ? ? H7);rewrite > Hletin;
      apply in_Skip;assumption]
  |(*FIXME*)generalize in match H2;intro;inversion H2
     [intros;simplify in H6;lapply (inj_head ? ? ? ? H6);rewrite > Hletin;
      simplify;apply in_Base
     |simplify;intros;lapply (inj_tail ? ? ? ? ? H8);rewrite > Hletin in H1;
      rewrite > H7 in H1;apply in_Skip;apply (H1 H5 H3)]]
qed.

lemma in_FV_subst : \forall x,T,U,n.(in_list ? x (fv_type T)) \to
                                (in_list ? x (fv_type (subst_type_nat T U n))).
intros 3;elim T
  [simplify in H;inversion H
     [intros;lapply (sym_eq ? ? ? H2);absurd (a::l = [])
        [assumption|apply nil_cons]
     |intros;lapply (sym_eq ? ? ? H4);absurd (a1::l = [])
        [assumption|apply nil_cons]]
  |2,3:simplify;simplify in H;assumption
  |*:simplify in H2;simplify;apply natinG_or_inH_to_natinGH;
   lapply (nat_in_list_case ? ? ? H2);elim Hletin
     [1,3:left;apply (H1 ? H3)
     |*:right;apply (H ? H3)]]
qed.

(*** lemma on fresh names ***)

lemma fresh_name : \forall l:(list nat).\exists n.\lnot (in_list ? n l).
cut (\forall l:(list nat).\exists n.\forall m.
        (n \leq m) \to \lnot (in_list ? m l))
  [intros;lapply (Hcut l);elim Hletin;apply ex_intro
     [apply a
     |apply H;constructor 1]
  |intros;elim l
    [apply ex_intro 
       [apply O
       |intros;unfold;intro;inversion H1
          [intros;lapply (sym_eq ? ? ? H3);absurd (a::l1 = [])
             [assumption|apply nil_cons]
          |intros;lapply (sym_eq ? ? ? H5);absurd (a1::l1 = [])
             [assumption|apply nil_cons]]]
    |elim H;lapply (decidable_eq_nat a t);elim Hletin
       [apply ex_intro
          [apply (S a)
          |intros;unfold;intro;inversion H4
             [intros;lapply (inj_head_nat ? ? ? ? H6);rewrite < Hletin1 in H5;
              rewrite < H2 in H5;rewrite > H5 in H3;
              apply (not_le_Sn_n ? H3)
             |intros;lapply (inj_tail ? ? ? ? ? H8);rewrite < Hletin1 in H5;
              rewrite < H7 in H5;
              apply (H1 m ? H5);lapply (le_S ? ? H3);
              apply (le_S_S_to_le ? ? Hletin2)]]
       |cut ((leb a t) = true \lor (leb a t) = false)
          [elim Hcut
             [apply ex_intro
                [apply (S t)
                |intros;unfold;intro;inversion H5
                   [intros;lapply (inj_head_nat ? ? ? ? H7);rewrite > H6 in H4;
                    rewrite < Hletin1 in H4;apply (not_le_Sn_n ? H4)
                   |intros;lapply (inj_tail ? ? ? ? ? H9);
                    rewrite < Hletin1 in H6;lapply (H1 a1)
                      [apply (Hletin2 H6)
                      |lapply (leb_to_Prop a t);rewrite > H3 in Hletin2;
                       simplify in Hletin2;rewrite < H8;
                       apply (trans_le ? ? ? Hletin2);
                       apply (trans_le ? ? ? ? H4);constructor 2;constructor 1]]]
             |apply ex_intro
                [apply a
                |intros;lapply (leb_to_Prop a t);rewrite > H3 in Hletin1;
                 simplify in Hletin1;lapply (not_le_to_lt ? ? Hletin1);
                 unfold in Hletin2;unfold;intro;inversion H5
                   [intros;lapply (inj_head_nat ? ? ? ? H7);
                    rewrite < Hletin3 in H6;rewrite > H6 in H4;
                    apply (Hletin1 H4)
                   |intros;lapply (inj_tail ? ? ? ? ? H9);
                    rewrite < Hletin3 in H6;rewrite < H8 in H6;
                    apply (H1 ? H4 H6)]]]
          |elim (leb a t);autobatch]]]]
qed.

(*** lemmata on well-formedness ***)

lemma fv_WFT : \forall T,x,G.(WFType G T) \to (in_list ? x (fv_type T)) \to
                  (in_list ? x (fv_env G)).
intros 4.elim H
  [simplify in H2;inversion H2
     [intros;lapply (inj_head_nat ? ? ? ? H4);rewrite < Hletin;assumption
     |intros;lapply (inj_tail ? ? ? ? ? H6);rewrite < Hletin in H3;
      inversion H3
        [intros;lapply (sym_eq ? ? ? H8);absurd (a2 :: l2 = []) 
           [assumption|apply nil_cons]
        |intros;lapply (sym_eq ? ? ? H10);
            absurd (a3 :: l2 = []) [assumption|apply nil_cons]]]
  |simplify in H1;lapply (in_list_nil ? x H1);elim Hletin
  |simplify in H5;lapply (nat_in_list_case ? ? ? H5);elim Hletin
     [apply (H4 H6)
     |apply (H2 H6)]
  |simplify in H5;lapply (nat_in_list_case ? ? ? H5);elim Hletin
     [lapply (fresh_name ((fv_type t1) @ (fv_env e)));elim Hletin1;
      cut ((\lnot (in_list ? a (fv_type t1))) \land
           (\lnot (in_list ? a (fv_env e))))
        [elim Hcut;lapply (H4 ? H9 H8)
           [cut (x \neq a)
              [simplify in Hletin2;
               (* FIXME trick *);generalize in match Hletin2;intro;
               inversion Hletin2
                 [intros;lapply (inj_head_nat ? ? ? ? H12);
                  rewrite < Hletin3 in H11;lapply (Hcut1 H11);elim Hletin4
                 |intros;lapply (inj_tail ? ? ? ? ? H14);rewrite > Hletin3;
                  assumption]
              |unfold;intro;apply H8;rewrite < H10;assumption]
           |rewrite > subst_O_nat;apply in_FV_subst;assumption]
        |split
           [unfold;intro;apply H7;apply natinG_or_inH_to_natinGH;right;
            assumption
           |unfold;intro;apply H7;apply natinG_or_inH_to_natinGH;left;
            assumption]]
     |apply (H2 H6)]]
qed.
           
(*** some exotic inductions and related lemmas ***) 

lemma not_t_len_lt_SO : \forall T.\lnot (t_len T) < (S O).
intros;elim T
  [1,2,3:simplify;unfold;intro;unfold in H;elim (not_le_Sn_n ? H)
  |*:simplify;unfold;rewrite > max_case;elim (leb (t_len t) (t_len t1))
     [1,3:simplify in H2;apply H1;apply (trans_lt ? ? ? ? H2);unfold;constructor 1
     |*:simplify in H2;apply H;apply (trans_lt ? ? ? ? H2);unfold;constructor 1]]
qed.

lemma Typ_len_ind : \forall P:Typ \to Prop.
                       (\forall U.(\forall V.((t_len V) < (t_len U)) \to (P V))
                           \to (P U))
                       \to \forall T.(P T).
cut (\forall P:Typ \to Prop.
        (\forall U.(\forall V.((t_len V) < (t_len U)) \to (P V))
            \to (P U))
        \to \forall T,n.(n = (t_len T)) \to (P T))                      
  [intros;apply (Hcut ? H ? (t_len T));reflexivity
  |intros 4;generalize in match T;apply (nat_elim1 n);intros;
   generalize in match H2;elim t 
     [1,2,3:apply H;intros;simplify in H4;elim (not_t_len_lt_SO ? H4)
     |*:apply H;intros;apply (H1 (t_len V))
        [1,3:rewrite > H5;assumption
        |*:reflexivity]]]
qed.

lemma t_len_arrow1 : \forall T1,T2.(t_len T1) < (t_len (Arrow T1 T2)).
intros.simplify.
(* FIXME!!! BUG?!?! *)
cut ((max (t_len T1) (t_len T2)) = match (leb (t_len T1) (t_len T2)) with
      [ false \Rightarrow (t_len T2)
      | true \Rightarrow (t_len T1) ])
  [rewrite > Hcut;cut ((leb (t_len T1) (t_len T2)) = false \lor
                       (leb (t_len T1) (t_len T2)) = true)
     [lapply (leb_to_Prop (t_len T1) (t_len T2));elim Hcut1
        [rewrite > H;rewrite > H in Hletin;simplify;constructor 1
        |rewrite > H;rewrite > H in Hletin;simplify;simplify in Hletin;
         unfold;apply le_S_S;assumption]
     |elim (leb (t_len T1) (t_len T2));autobatch]
  |elim T1;simplify;reflexivity]
qed.

lemma t_len_arrow2 : \forall T1,T2.(t_len T2) < (t_len (Arrow T1 T2)).
intros.simplify.
(* FIXME!!! BUG?!?! *)
cut ((max (t_len T1) (t_len T2)) = match (leb (t_len T1) (t_len T2)) with
      [ false \Rightarrow (t_len T2)
      | true \Rightarrow (t_len T1) ])
  [rewrite > Hcut;cut ((leb (t_len T1) (t_len T2)) = false \lor
                       (leb (t_len T1) (t_len T2)) = true)
     [lapply (leb_to_Prop (t_len T1) (t_len T2));elim Hcut1
        [rewrite > H;rewrite > H in Hletin;simplify;simplify in Hletin;
         lapply (not_le_to_lt ? ? Hletin);unfold in Hletin1;unfold;
         constructor 2;assumption
        |rewrite > H;simplify;unfold;constructor 1]
     |elim (leb (t_len T1) (t_len T2));autobatch]
  |elim T1;simplify;reflexivity]
qed.

lemma t_len_forall1 : \forall T1,T2.(t_len T1) < (t_len (Forall T1 T2)).
intros.simplify.
(* FIXME!!! BUG?!?! *)
cut ((max (t_len T1) (t_len T2)) = match (leb (t_len T1) (t_len T2)) with
      [ false \Rightarrow (t_len T2)
      | true \Rightarrow (t_len T1) ])
  [rewrite > Hcut;cut ((leb (t_len T1) (t_len T2)) = false \lor
                       (leb (t_len T1) (t_len T2)) = true)
     [lapply (leb_to_Prop (t_len T1) (t_len T2));elim Hcut1
        [rewrite > H;rewrite > H in Hletin;simplify;constructor 1
        |rewrite > H;rewrite > H in Hletin;simplify;simplify in Hletin;
         unfold;apply le_S_S;assumption]
     |elim (leb (t_len T1) (t_len T2));autobatch]
  |elim T1;simplify;reflexivity]
qed.

lemma t_len_forall2 : \forall T1,T2.(t_len T2) < (t_len (Forall T1 T2)).
intros.simplify.
(* FIXME!!! BUG?!?! *)
cut ((max (t_len T1) (t_len T2)) = match (leb (t_len T1) (t_len T2)) with
      [ false \Rightarrow (t_len T2)
      | true \Rightarrow (t_len T1) ])
  [rewrite > Hcut;cut ((leb (t_len T1) (t_len T2)) = false \lor
                       (leb (t_len T1) (t_len T2)) = true)
     [lapply (leb_to_Prop (t_len T1) (t_len T2));elim Hcut1
        [rewrite > H;rewrite > H in Hletin;simplify;simplify in Hletin;
         lapply (not_le_to_lt ? ? Hletin);unfold in Hletin1;unfold;
         constructor 2;assumption
        |rewrite > H;simplify;unfold;constructor 1]
     |elim (leb (t_len T1) (t_len T2));autobatch]
  |elim T1;simplify;reflexivity]
qed.

lemma eq_t_len_TFree_subst : \forall T,n,X.(t_len T) = 
                                         (t_len (subst_type_nat T (TFree X) n)).
intro.elim T
  [simplify;elim (eqb n n1);simplify;reflexivity
  |2,3:simplify;reflexivity
  |simplify;lapply (H n X);lapply (H1 n X);rewrite < Hletin;rewrite < Hletin1;
   reflexivity
  |simplify;lapply (H n X);lapply (H1 (S n) X);rewrite < Hletin;
   rewrite < Hletin1;reflexivity]
qed.

(*** lemmata relating subtyping and well-formedness ***)

lemma JS_to_WFE : \forall G,T,U.(G \vdash T \lessdot U) \to (WFEnv G).
intros;elim H;assumption.
qed.

lemma JS_to_WFT : \forall G,T,U.(JSubtype G T U) \to ((WFType G T) \land 
                                                      (WFType G U)).
intros;elim H
  [split [assumption|apply WFT_Top]
  |split;apply WFT_TFree;assumption
  |split 
     [apply WFT_TFree;apply boundinenv_natinfv;apply ex_intro
        [apply true | apply ex_intro [apply t1 |assumption]]
     |elim H3;assumption]
  |elim H2;elim H4;split;apply WFT_Arrow;assumption
  |elim H2;split
     [apply (WFT_Forall ? ? ? H6);intros;elim (H4 X H7);
      apply (WFT_env_incl ? ? H9);simplify;unfold;intros;assumption
     |apply (WFT_Forall ? ? ? H5);intros;elim (H4 X H7);
      apply (WFT_env_incl ? ? H10);simplify;unfold;intros;assumption]]
qed.

lemma JS_to_WFT1 : \forall G,T,U.(JSubtype G T U) \to (WFType G T).
intros;lapply (JS_to_WFT ? ? ? H);elim Hletin;assumption.
qed.

lemma JS_to_WFT2 : \forall G,T,U.(JSubtype G T U) \to (WFType G U).
intros;lapply (JS_to_WFT ? ? ? H);elim Hletin;assumption.
qed.

lemma WFE_Typ_subst : \forall H,x,B,C,T,U,G.
                      (WFEnv (H @ ((mk_bound B x T) :: G))) \to (WFType G U) \to
                      (WFEnv (H @ ((mk_bound C x U) :: G))).
intros 7;elim H 0
  [simplify;intros;(*FIXME*)generalize in match H1;intro;inversion H1
     [intros;lapply (nil_cons ? G (mk_bound B x T));lapply (Hletin H4);
      elim Hletin1
     |intros;lapply (inj_tail ? ? ? ? ? H8);lapply (inj_head ? ? ? ? H8);
      destruct Hletin1;rewrite < Hletin in H6;rewrite < Hletin in H4;
      rewrite < Hcut1 in H6;apply (WFE_cons ? ? ? ? H4 H6 H2)]
  |intros;simplify;generalize in match H2;elim t;simplify in H4;
   inversion H4
     [intros;absurd (mk_bound b n t1::l@(mk_bound B x T::G)=Empty)
        [assumption
        |apply nil_cons]
     |intros;lapply (inj_tail ? ? ? ? ? H9);lapply (inj_head ? ? ? ? H9);
      destruct Hletin1;apply WFE_cons
        [apply H1
           [rewrite > Hletin;assumption
           |assumption]
        |rewrite > Hcut1;generalize in match H7;rewrite < Hletin;
         rewrite > (fv_env_extends ? x B C T U);intro;assumption
        |rewrite < Hletin in H8;rewrite > Hcut2;
         apply (WFT_env_incl ? ? H8);rewrite > (fv_env_extends ? x B C T U);
         unfold;intros;assumption]]]
qed.

lemma WFE_bound_bound : \forall B,x,T,U,G. (WFEnv G) \to
                                  (in_list ? (mk_bound B x T) G) \to
                                  (in_list ? (mk_bound B x U) G) \to T = U.
intros 6;elim H
  [lapply (in_list_nil ? ? H1);elim Hletin
  |inversion H6
     [intros;rewrite < H7 in H8;lapply (inj_head ? ? ? ? H8);
      rewrite > Hletin in H5;inversion H5
        [intros;rewrite < H9 in H10;lapply (inj_head ? ? ? ? H10);
         destruct Hletin1;symmetry;assumption
        |intros;lapply (inj_tail ? ? ? ? ? H12);rewrite < Hletin1 in H9;
         rewrite < H11 in H9;lapply (boundinenv_natinfv x e)
           [destruct Hletin;rewrite < Hcut1 in Hletin2;lapply (H3 Hletin2);
            elim Hletin3
           |apply ex_intro
              [apply B|apply ex_intro [apply T|assumption]]]]
     |intros;lapply (inj_tail ? ? ? ? ? H10);rewrite < H9 in H7;
      rewrite < Hletin in H7;(*FIXME*)generalize in match H5;intro;inversion H5
        [intros;rewrite < H12 in H13;lapply (inj_head ? ? ? ? H13);
         destruct Hletin1;rewrite < Hcut1 in H7;
         lapply (boundinenv_natinfv n e)
           [lapply (H3 Hletin2);elim Hletin3
           |apply ex_intro
              [apply B|apply ex_intro [apply U|assumption]]]
        |intros;apply (H2 ? H7);rewrite > H14;lapply (inj_tail ? ? ? ? ? H15);
         rewrite > Hletin1;assumption]]]
qed.
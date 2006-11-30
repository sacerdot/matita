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

set "baseuri" "cic:/matita/library/Fsub/defn".
include "logic/equality.ma".
include "nat/nat.ma".
include "datatypes/bool.ma".
include "nat/compare.ma".
include "list/list.ma".

(*** useful definitions and lemmas not really related to Fsub ***)

lemma eqb_case : \forall x,y.(eqb x y) = true \lor (eqb x y) = false.
intros;elim (eqb x y);auto;
qed.
       
lemma eq_eqb_case : \forall x,y.((x = y) \land (eqb x y) = true) \lor
                                ((x \neq y) \land (eqb x y) = false).
intros;lapply (eqb_to_Prop x y);elim (eqb_case x y)
  [rewrite > H in Hletin;simplify in Hletin;left;auto
  |rewrite > H in Hletin;simplify in Hletin;right;auto]
qed.

let rec max m n \def
  match (leb m n) with
     [true \Rightarrow n
     |false \Rightarrow m]. 

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
  
notation "hvbox(\Forall S. break T)" 
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

interpretation "universal type" 'forall S T = (cic:/matita/test/Typ.ind#xpointer(1/1/5) S T).

interpretation "bound var" 'var x = (cic:/matita/test/Typ.ind#xpointer(1/1/1) x).

interpretation "bound tvar" 'tvar x = (cic:/matita/test/Typ.ind#xpointer(1/1/3) x).

interpretation "bound tname" 'tname x = (cic:/matita/test/Typ.ind#xpointer(1/1/2) x).

interpretation "arrow type" 'arrow S T = (cic:/matita/test/Typ.ind#xpointer(1/1/4) S T). 

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

(* 
let rec fresh_name G n \def
  match G with
    [ nil \Rightarrow n
    | (cons b H) \Rightarrow match (leb (fresh_name H n) (name b)) with
      [ true \Rightarrow (S (name b))
      | false \Rightarrow (fresh_name H n) ]].

lemma freshname_Gn_geq_n : \forall G,n.((fresh_name G n) >= n).
intro;elim G
  [simplify;unfold;constructor 1
  |simplify;cut ((leb (fresh_name l n) (name s)) = true \lor
                 (leb (fresh_name l n) (name s) = false))
     [elim Hcut
        [lapply (leb_to_Prop (fresh_name l n) (name s));rewrite > H1 in Hletin;
         simplify in Hletin;rewrite > H1;simplify;lapply (H n);
         unfold in Hletin1;unfold;
         apply (trans_le ? ? ? Hletin1);
         apply (trans_le ? ? ? Hletin);constructor 2;constructor 1
        |rewrite > H1;simplify;apply H]
     |elim (leb (fresh_name l n) (name s)) [left;reflexivity|right;reflexivity]]]
qed.

lemma freshname_consGX_gt_X : \forall G,X,T,b,n.
          (fresh_name (cons ? (mk_bound b X T) G) n) > X.
intros.unfold.unfold.simplify.cut ((leb (fresh_name G n) X) = true \lor 
                                   (leb (fresh_name G n) X) = false)
  [elim Hcut
     [rewrite > H;simplify;constructor 1
     |rewrite > H;simplify;lapply (leb_to_Prop (fresh_name G n) X);
      rewrite > H in Hletin;simplify in Hletin;
      lapply (not_le_to_lt ? ? Hletin);unfold in Hletin1;assumption]
  |elim (leb (fresh_name G n) X) [left;reflexivity|right;reflexivity]]
qed.

lemma freshname_case : \forall G,X,T,b,n.
  (fresh_name ((mk_bound b X T) :: G) n) = (fresh_name G n) \lor
  (fresh_name ((mk_bound b X T) :: G) n) = (S X).
intros.simplify.cut ((leb (fresh_name G n) X) = true \lor
                 (leb (fresh_name G n) X) = false)
  [elim Hcut
     [rewrite > H;simplify;right;reflexivity
     |rewrite > H;simplify;left;reflexivity]
  |elim (leb (fresh_name G n) X)
     [left;reflexivity|right;reflexivity]]
qed.

lemma freshname_monotone_n : \forall G,m,n.(m \leq n) \to
                             ((fresh_name G m) \leq (fresh_name G n)).
intros.elim G
  [simplify;assumption
  |simplify;cut ((leb (fresh_name l m) (name s)) = true \lor
                 (leb (fresh_name l m) (name s)) = false)
     [cut ((leb (fresh_name l n) (name s)) = true \lor
              (leb (fresh_name l n) (name s)) = false)
        [elim Hcut
           [rewrite > H2;simplify;elim Hcut1
              [rewrite > H3;simplify;constructor 1 
              |rewrite > H3;simplify;
               lapply (leb_to_Prop (fresh_name l n) (name s));
               rewrite > H3 in Hletin;simplify in Hletin;
               lapply (not_le_to_lt ? ? Hletin);unfold in Hletin1;assumption]
           |rewrite > H2;simplify;elim Hcut1
              [rewrite > H3;simplify;
               lapply (leb_to_Prop (fresh_name l m) (name s));
               rewrite > H2 in Hletin;simplify in Hletin;
               lapply (not_le_to_lt ? ? Hletin);unfold in Hletin1;
               lapply (leb_to_Prop (fresh_name l n) (name s));
               rewrite > H3 in Hletin2;
               simplify in Hletin2;lapply (trans_le ? ? ? Hletin1 H1);
               lapply (trans_le ? ? ? Hletin3 Hletin2);
               absurd ((S (name s)) \leq (name s))
                 [assumption|apply not_le_Sn_n]
              |rewrite > H3;simplify;assumption]]
        |elim (leb (fresh_name l n) (name s)) 
           [left;reflexivity|right;reflexivity]]
     |elim (leb (fresh_name l m) (name s)) [left;reflexivity|right;reflexivity]]]
qed.

lemma freshname_monotone_G : \forall G,X,T,b,n.
                   (fresh_name G n) \leq (fresh_name ((mk_bound b X T) :: G) n).
intros.simplify.cut ((leb (fresh_name G n) X) = true \lor
                     (leb (fresh_name G n) X) = false)
  [elim Hcut
     [rewrite > H;simplify;lapply (leb_to_Prop (fresh_name G n) X);
      rewrite > H in Hletin;simplify in Hletin;constructor 2;assumption
     |rewrite > H;simplify;constructor 1]
  |elim (leb (fresh_name G n) X)
     [left;reflexivity|right;reflexivity]]
qed.*)

lemma subst_O_nat : \forall T,U.((subst_type_O T U) = (subst_type_nat T U O)).
intros;elim T;simplify;reflexivity;
qed.

(* FIXME: these definitions shouldn't be part of the poplmark challenge
   - use destruct instead, when hopefully it will get fixed... *) 

definition head \def
  \lambda G:(list bound).match G with
    [ nil \Rightarrow (mk_bound false O Top)
    | (cons b H) \Rightarrow b].

definition head_nat \def
  \lambda G:(list nat).match G with
    [ nil \Rightarrow O
    | (cons n H) \Rightarrow n].

lemma inj_head : \forall h1,h2:bound.\forall t1,t2:Env.
                 ((h1::t1) = (h2::t2)) \to (h1 = h2).
intros.lapply (eq_f ? ? head ? ? H).simplify in Hletin.assumption.
qed.

lemma inj_head_nat : \forall h1,h2:nat.\forall t1,t2:(list nat).
                 ((h1::t1) = (h2::t2)) \to (h1 = h2).
intros.lapply (eq_f ? ? head_nat ? ? H).simplify in Hletin.assumption.
qed.

lemma inj_tail : \forall A.\forall h1,h2:A.\forall t1,t2:(list A).
                 ((h1::t1) = (h2::t2)) \to (t1 = t2).
intros.lapply (eq_f ? ? (tail ?) ? ? H).simplify in Hletin.assumption.
qed.

(* end of fixme *) 

(*** definitions and theorems about lists ***)

inductive in_list (A : Set) : A \to (list A) \to Prop \def
  | in_Base : \forall x:A.\forall l:(list A).
              (in_list A x (x :: l))
  | in_Skip : \forall x,y:A.\forall l:(list A).
              (in_list A x l) \to (in_list A x (y :: l)).

(* var binding is in env judgement *)                
definition var_bind_in_env : bound \to Env \to Prop \def
  \lambda b,G.(in_list bound b G).

(* FIXME: use the map in library/list (when there will be one) *)
definition map : \forall A,B,f.((list A) \to (list B)) \def
  \lambda A,B,f.let rec map (l : (list A)) : (list B) \def
    match l in list return \lambda l0:(list A).(list B) with
      [nil \Rightarrow (nil B)
      |(cons (a:A) (t:(list A))) \Rightarrow 
        (cons B (f a) (map t))] in map.

definition fv_env : (list bound) \to (list nat) \def
  \lambda G.(map ? ? (\lambda b.match b with
      [(mk_bound B X T) \Rightarrow X]) G).

(* variable is in env judgement *)              
definition var_in_env : nat \to Env \to Prop \def
  \lambda x,G.(in_list nat x (fv_env G)).
  
definition var_type_in_env : nat \to Env \to Prop \def
  \lambda x,G.\exists T.(var_bind_in_env (mk_bound true x T) G).

definition incl : \forall A.(list A) \to (list A) \to Prop \def
  \lambda A,l,m.\forall x.(in_list A x l) \to (in_list A x m).               
              
let rec fv_type T \def
  match T with
    [(TVar n) \Rightarrow []
    |(TFree x) \Rightarrow [x]
    |Top \Rightarrow []
    |(Arrow U V) \Rightarrow ((fv_type U) @ (fv_type V))
    |(Forall U V) \Rightarrow ((fv_type U) @ (fv_type V))].

lemma var_notinbG_notinG : \forall G,x,b.
                           (\lnot (var_in_env x (b::G))) 
                           \to \lnot (var_in_env x G).
intros 3.elim b.unfold.intro.elim H.unfold.simplify.constructor 2.exact H1.
qed.

lemma in_list_nil : \forall A,x.\lnot (in_list A x []).
intros.unfold.intro.inversion H
  [intros;lapply (sym_eq ? ? ? H2);absurd (a::l = [])
     [assumption|apply nil_cons]
  |intros;lapply (sym_eq ? ? ? H4);absurd (a1::l = [])
     [assumption|apply nil_cons]]
qed.

lemma notin_cons : \forall A,x,y,l.\lnot (in_list A x (y::l)) \to
                      (y \neq x) \land \lnot (in_list A x l).
intros.split
  [unfold;intro;apply H;rewrite > H1;constructor 1
  |unfold;intro;apply H;constructor 2;assumption]
qed.

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
  |intros 3;elim s;simplify in H1;inversion H1
     [intros;rewrite < H2;simplify;apply ex_intro
        [apply b
        |apply ex_intro
           [apply t
           |lapply (inj_head_nat ? ? ? ? H3);rewrite > H2;rewrite < Hletin;
            apply in_Base]]
     |intros;lapply (inj_tail ? ? ? ? ? H5);rewrite < Hletin in H2;
      rewrite < H4 in H2;lapply (H H2);elim Hletin1;elim H6;apply ex_intro
        [apply a2
        |apply ex_intro
           [apply a3
           |apply in_Skip;rewrite < H4;assumption]]]]
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

(* lemma incl_cons : \forall x,l1,l2.
                  (incl bound l1 l2) \to (incl bound (x :: l1) (x :: l2)).
intros.unfold in H.unfold.intros.inversion H1
  [intros;lapply (inj_head ? ? ? ? H3);rewrite > Hletin;apply in_Base
  |intros;apply in_Skip;apply H;lapply (inj_tail ? ? ? ? ? H5);rewrite > Hletin;
   assumption]
qed. *)

lemma incl_nat_cons : \forall x,l1,l2.
                  (incl nat l1 l2) \to (incl nat (x :: l1) (x :: l2)).
intros.unfold in H.unfold.intros.inversion H1
  [intros;lapply (inj_head_nat ? ? ? ? H3);rewrite > Hletin;apply in_Base
  |intros;apply in_Skip;apply H;lapply (inj_tail ? ? ? ? ? H5);rewrite > Hletin;
   assumption]
qed.

lemma boundin_envappend_case : \forall G,H,b.(var_bind_in_env b (H @ G)) \to 
                               (var_bind_in_env b G) \lor (var_bind_in_env b H).
intros 3.elim H
  [simplify in H1;left;assumption
  |unfold in H2;inversion H2
    [intros;simplify in H4;lapply (inj_head ? ? ? ? H4);rewrite > Hletin;
     right;apply in_Base
    |intros;simplify in H6;lapply (inj_tail ? ? ? ? ? H6);rewrite < Hletin in H3;
     rewrite > H5 in H1;lapply (H1 H3);elim Hletin1
       [left;assumption|right;apply in_Skip;assumption]]]
qed.

lemma varin_envappend_case: \forall G,H,x.(var_in_env x (H @ G)) \to
                            (var_in_env x G) \lor (var_in_env x H).
intros 3.elim H 0
  [simplify;intro;left;assumption
  |intros 2;elim s;simplify in H2;inversion H2
     [intros;lapply (inj_head_nat ? ? ? ? H4);rewrite > Hletin;right;
      simplify;constructor 1
     |intros;lapply (inj_tail ? ? ? ? ? H6);
      lapply H1
        [rewrite < H5;elim Hletin1
           [left;assumption|right;simplify;constructor 2;assumption]
        |unfold var_in_env;unfold fv_env;rewrite > Hletin;rewrite > H5;
         assumption]]]
qed.

lemma boundinG_or_boundinH_to_boundinGH : \forall G,H,b.
                      (var_bind_in_env b G) \lor (var_bind_in_env b H) \to
                      (var_bind_in_env b (H @ G)).
intros.elim H1
  [elim H
     [simplify;assumption
     |simplify;apply in_Skip;assumption]
  |generalize in match H2;elim H2
     [simplify;apply in_Base
     |lapply (H4 H3);simplify;apply in_Skip;assumption]]
qed. 


lemma varinG_or_varinH_to_varinGH : \forall G,H,x.
                          (var_in_env x G) \lor (var_in_env x H) \to
                          (var_in_env x (H @ G)).
intros.elim H1 0
  [elim H
     [simplify;assumption
     |elim s;simplify;constructor 2;apply (H2 H3)]
  |elim H 0
     [simplify;intro;lapply (in_list_nil nat x H2);elim Hletin
     |intros 2;elim s;simplify in H3;inversion H3
        [intros;lapply (inj_head_nat ? ? ? ? H5);rewrite > Hletin;simplify;
         constructor 1
        |intros;simplify;constructor 2;rewrite < H6;apply H2;
         lapply (inj_tail ? ? ? ? ? H7);rewrite > H6;unfold;unfold fv_env;
         rewrite > Hletin;assumption]]]
qed.

lemma varbind_to_append : \forall G,b.(var_bind_in_env b G) \to
                          \exists G1,G2.(G = (G2 @ (b :: G1))).
intros.generalize in match H.elim H
  [apply ex_intro [apply l|apply ex_intro [apply Empty|reflexivity]]
  |lapply (H2 H1);elim Hletin;elim H4;rewrite > H5;
   apply ex_intro 
     [apply a2|apply ex_intro [apply (a1 :: a3)|simplify;reflexivity]]]
qed.
  
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


lemma WFT_env_incl : \forall G,T.(WFType G T) \to
                     \forall H.(incl ? (fv_env G) (fv_env H)) \to (WFType H T).
intros 4.generalize in match H1.elim H
  [apply WFT_TFree;unfold in H3;apply (H3 ? H2)
  |apply WFT_Top
  |apply WFT_Arrow [apply (H3 ? H6)|apply (H5 ? H6)]
  |apply WFT_Forall 
     [apply (H3 ? H6)
     |intros;apply H5
        [unfold;intro;unfold in H7;apply H7;unfold in H6;apply(H6 ? H9)
        |assumption
        |simplify;apply (incl_nat_cons ? ? ? H6)]]]
qed.

(*** definitions and theorems about swaps ***)

definition swap : nat \to nat \to nat \to nat \def
  \lambda u,v,x.match (eqb x u) with
    [true \Rightarrow v
    |false \Rightarrow match (eqb x v) with
       [true \Rightarrow u
       |false \Rightarrow x]].
       
lemma swap_left : \forall x,y.(swap x y x) = y.
intros;unfold swap;rewrite > eqb_n_n;simplify;reflexivity;
qed.

lemma swap_right : \forall x,y.(swap x y y) = x.
intros;unfold swap;elim (eq_eqb_case y x)
  [elim H;rewrite > H2;simplify;rewrite > H1;reflexivity
  |elim H;rewrite > H2;simplify;rewrite > eqb_n_n;simplify;reflexivity]
qed.

lemma swap_other : \forall x,y,z.(z \neq x) \to (z \neq y) \to (swap x y z) = z.
intros;unfold swap;elim (eq_eqb_case z x)
  [elim H2;lapply (H H3);elim Hletin
  |elim H2;rewrite > H4;simplify;elim (eq_eqb_case z y)
     [elim H5;lapply (H1 H6);elim Hletin
     |elim H5;rewrite > H7;simplify;reflexivity]]
qed. 

lemma swap_inv : \forall u,v,x.(swap u v (swap u v x)) = x.
intros;unfold in match (swap u v x);elim (eq_eqb_case x u)
  [elim H;rewrite > H2;simplify;rewrite > H1;apply swap_right
  |elim H;rewrite > H2;simplify;elim (eq_eqb_case x v)
     [elim H3;rewrite > H5;simplify;rewrite > H4;apply swap_left
     |elim H3;rewrite > H5;simplify;apply (swap_other ? ? ? H1 H4)]]
qed.

lemma swap_inj : \forall u,v,x,y.(swap u v x) = (swap u v y) \to x = y.
intros;unfold swap in H;elim (eq_eqb_case x u)
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
qed. 

lemma fv_subst_type_nat : \forall x,T,y,n.(in_list ? x (fv_type T)) \to
                         (in_list ? x (fv_type (subst_type_nat T (TFree y) n))).
intros 3;elim T 0
  [intros;simplify in H;elim (in_list_nil ? ? H)
  |simplify;intros;assumption
  |simplify;intros;assumption
  |intros;simplify in H2;elim (nat_in_list_case ? ? ? H2)
     [simplify;apply natinG_or_inH_to_natinGH;left;apply (H1 ? H3)
     |simplify;apply natinG_or_inH_to_natinGH;right;apply (H ? H3)]
  |intros;simplify in H2;elim (nat_in_list_case ? ? ? H2)
     [simplify;apply natinG_or_inH_to_natinGH;left;apply (H1 ? H3)
     |simplify;apply natinG_or_inH_to_natinGH;right;apply (H ? H3)]]
qed.

lemma fv_subst_type_O : \forall x,T,y.(in_list ? x (fv_type T)) \to
                         (in_list ? x (fv_type (subst_type_O T (TFree y)))).
intros;rewrite > subst_O_nat;apply (fv_subst_type_nat ? ? ? ? H);
qed.

let rec swap_Typ u v T on T \def
  match T with
     [(TVar n) \Rightarrow (TVar n)
     |(TFree X) \Rightarrow (TFree (swap u v X))
     |Top \Rightarrow Top
     |(Arrow T1 T2) \Rightarrow (Arrow (swap_Typ u v T1) (swap_Typ u v T2))
     |(Forall T1 T2) \Rightarrow (Forall (swap_Typ u v T1) (swap_Typ u v T2))].
     
lemma swap_Typ_inv : \forall u,v,T.(swap_Typ u v (swap_Typ u v T)) = T.
intros;elim T
  [simplify;reflexivity
  |simplify;rewrite > swap_inv;reflexivity
  |simplify;reflexivity
  |simplify;rewrite > H;rewrite > H1;reflexivity
  |simplify;rewrite > H;rewrite > H1;reflexivity]
qed.

lemma swap_Typ_not_free : \forall u,v,T.\lnot (in_list ? u (fv_type T)) \to
                      \lnot (in_list ? v (fv_type T)) \to (swap_Typ u v T) = T.
intros 3;elim T 0
  [intros;simplify;reflexivity
  |simplify;intros;cut (n \neq u \land n \neq v)
     [elim Hcut;rewrite > (swap_other ? ? ? H2 H3);reflexivity
     |split
        [unfold;intro;apply H;rewrite > H2;apply in_Base
        |unfold;intro;apply H1;rewrite > H2;apply in_Base]]
  |simplify;intros;reflexivity
  |simplify;intros;cut ((\lnot (in_list ? u (fv_type t)) \land
                         \lnot (in_list ? u (fv_type t1))) \land
                        (\lnot (in_list ? v (fv_type t)) \land
                         \lnot (in_list ? v (fv_type t1))))
     [elim Hcut;elim H4;elim H5;clear Hcut H4 H5;rewrite > (H H6 H8);
      rewrite > (H1 H7 H9);reflexivity
     |split
        [split;unfold;intro;apply H2;apply natinG_or_inH_to_natinGH;auto
        |split;unfold;intro;apply H3;apply natinG_or_inH_to_natinGH;auto]]
  |simplify;intros;cut ((\lnot (in_list ? u (fv_type t)) \land
                         \lnot (in_list ? u (fv_type t1))) \land
                        (\lnot (in_list ? v (fv_type t)) \land
                         \lnot (in_list ? v (fv_type t1))))
     [elim Hcut;elim H4;elim H5;clear Hcut H4 H5;rewrite > (H H6 H8);
      rewrite > (H1 H7 H9);reflexivity
     |split
        [split;unfold;intro;apply H2;apply natinG_or_inH_to_natinGH;auto
        |split;unfold;intro;apply H3;apply natinG_or_inH_to_natinGH;auto]]]
qed.
        
lemma subst_type_nat_swap : \forall u,v,T,X,m.
         (swap_Typ u v (subst_type_nat T (TFree X) m)) =
         (subst_type_nat (swap_Typ u v T) (TFree (swap u v X)) m).
intros 4;elim T
  [simplify;elim (eqb_case n m);rewrite > H;simplify;reflexivity
  |simplify;reflexivity
  |simplify;reflexivity
  |simplify;rewrite > H;rewrite > H1;reflexivity
  |simplify;rewrite > H;rewrite > H1;reflexivity]
qed.

lemma subst_type_O_swap : \forall u,v,T,X.
         (swap_Typ u v (subst_type_O T (TFree X))) =
         (subst_type_O (swap_Typ u v T) (TFree (swap u v X))).
intros 4;rewrite > (subst_O_nat (swap_Typ u v T));rewrite > (subst_O_nat T);
apply subst_type_nat_swap;
qed.

lemma in_fv_type_swap : \forall u,v,x,T.((in_list ? x (fv_type T)) \to
              (in_list ? (swap u v x) (fv_type (swap_Typ u v T)))) \land
             ((in_list ? (swap u v x) (fv_type (swap_Typ u v T))) \to
              (in_list ? x (fv_type T))).
intros;split
  [elim T 0
     [simplify;intros;elim (in_list_nil ? ? H)
     |simplify;intros;cut (x = n)
        [rewrite > Hcut;apply in_Base
        |inversion H
           [intros;lapply (inj_head_nat ? ? ? ? H2);rewrite > Hletin;
            reflexivity
           |intros;lapply (inj_tail ? ? ? ? ? H4);rewrite < Hletin in H1;
            elim (in_list_nil ? ? H1)]]
     |simplify;intro;elim (in_list_nil ? ? H)
     |simplify;intros;elim (nat_in_list_case ? ? ? H2)
        [apply natinG_or_inH_to_natinGH;left;apply (H1 H3)
        |apply natinG_or_inH_to_natinGH;right;apply (H H3)]
     |simplify;intros;elim (nat_in_list_case ? ? ? H2)
        [apply natinG_or_inH_to_natinGH;left;apply (H1 H3)
        |apply natinG_or_inH_to_natinGH;right;apply (H H3)]]
  |elim T 0
     [simplify;intros;elim (in_list_nil ? ? H)
     |simplify;intros;cut ((swap u v x) = (swap u v n))
        [lapply (swap_inj ? ? ? ? Hcut);rewrite > Hletin;apply in_Base
        |inversion H
           [intros;lapply (inj_head_nat ? ? ? ? H2);rewrite > Hletin;
            reflexivity
           |intros;lapply (inj_tail ? ? ? ? ? H4);rewrite < Hletin in H1;
            elim (in_list_nil ? ? H1)]]
     |simplify;intro;elim (in_list_nil ? ? H)
     |simplify;intros;elim (nat_in_list_case ? ? ? H2)
        [apply natinG_or_inH_to_natinGH;left;apply (H1 H3)
        |apply natinG_or_inH_to_natinGH;right;apply (H H3)]
     |simplify;intros;elim (nat_in_list_case ? ? ? H2)
        [apply natinG_or_inH_to_natinGH;left;apply (H1 H3)
        |apply natinG_or_inH_to_natinGH;right;apply (H H3)]]]
qed.
        
definition swap_bound : nat \to nat \to bound \to bound \def
  \lambda u,v,b.match b with
     [(mk_bound B X T) \Rightarrow (mk_bound B (swap u v X) (swap_Typ u v T))].

definition swap_Env : nat \to nat \to Env \to Env \def
  \lambda u,v,G.(map ? ? (\lambda b.(swap_bound u v b)) G). 

lemma lookup_swap : \forall x,u,v,T,B,G.(in_list ? (mk_bound B x T) G) \to
    (in_list ? (mk_bound B (swap u v x) (swap_Typ u v T)) (swap_Env u v G)).
intros 6;elim G 0
  [intros;elim (in_list_nil ? ? H)
  |intro;elim s;simplify;inversion H1
     [intros;lapply (inj_head ? ? ? ? H3);rewrite < H2 in Hletin;
      destruct Hletin;rewrite > Hcut;rewrite > Hcut1;rewrite > Hcut2;
      apply in_Base
     |intros;lapply (inj_tail ? ? ? ? ? H5);rewrite < Hletin in H2;
      rewrite < H4 in H2;apply in_Skip;apply (H H2)]]
qed.

lemma in_FV_subst : \forall x,T,U,n.(in_list ? x (fv_type T)) \to
                                (in_list ? x (fv_type (subst_type_nat T U n))).
intros 3;elim T
  [simplify in H;inversion H
     [intros;lapply (sym_eq ? ? ? H2);absurd (a::l = [])
        [assumption|apply nil_cons]
     |intros;lapply (sym_eq ? ? ? H4);absurd (a1::l = [])
        [assumption|apply nil_cons]]
  |simplify;simplify in H;assumption
  |simplify in H;simplify;assumption
  |simplify in H2;simplify;apply natinG_or_inH_to_natinGH;
   lapply (nat_in_list_case ? ? ? H2);elim Hletin
     [left;apply (H1 ? H3)
     |right;apply (H ? H3)]
  |simplify in H2;simplify;apply natinG_or_inH_to_natinGH;
   lapply (nat_in_list_case ? ? ? H2);elim Hletin
     [left;apply (H1 ? H3)
     |right;apply (H ? H3)]]
qed.

lemma in_dom_swap : \forall u,v,x,G.
                       ((in_list ? x (fv_env G)) \to 
                       (in_list ? (swap u v x) (fv_env (swap_Env u v G)))) \land
                       ((in_list ? (swap u v x) (fv_env (swap_Env u v G))) \to
                       (in_list ? x (fv_env G))).
intros;split
  [elim G 0
     [simplify;intro;elim (in_list_nil ? ? H)
     |intro;elim s 0;simplify;intros;inversion H1
        [intros;lapply (inj_head_nat ? ? ? ? H3);rewrite > Hletin;apply in_Base
        |intros;lapply (inj_tail ? ? ? ? ? H5);rewrite < Hletin in H2;
         rewrite > H4 in H;apply in_Skip;apply (H H2)]]
  |elim G 0
     [simplify;intro;elim (in_list_nil ? ? H)
     |intro;elim s 0;simplify;intros;inversion H1
        [intros;lapply (inj_head_nat ? ? ? ? H3);rewrite < H2 in Hletin;
         lapply (swap_inj ? ? ? ? Hletin);rewrite > Hletin1;apply in_Base
        |intros;lapply (inj_tail ? ? ? ? ? H5);rewrite < Hletin in H2;
         rewrite > H4 in H;apply in_Skip;apply (H H2)]]]
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
    |elim H;lapply (decidable_eq_nat a s);elim Hletin
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
       |cut ((leb a s) = true \lor (leb a s) = false)
          [elim Hcut
             [apply ex_intro
                [apply (S s)
                |intros;unfold;intro;inversion H5
                   [intros;lapply (inj_head_nat ? ? ? ? H7);rewrite > H6 in H4;
                    rewrite < Hletin1 in H4;apply (not_le_Sn_n ? H4)
                   |intros;lapply (inj_tail ? ? ? ? ? H9);
                    rewrite < Hletin1 in H6;lapply (H1 a1)
                      [apply (Hletin2 H6)
                      |lapply (leb_to_Prop a s);rewrite > H3 in Hletin2;
                       simplify in Hletin2;rewrite < H8;
                       apply (trans_le ? ? ? Hletin2);
                       apply (trans_le ? ? ? ? H4);constructor 2;constructor 1]]]
             |apply ex_intro
                [apply a
                |intros;lapply (leb_to_Prop a s);rewrite > H3 in Hletin1;
                 simplify in Hletin1;lapply (not_le_to_lt ? ? Hletin1);
                 unfold in Hletin2;unfold;intro;inversion H5
                   [intros;lapply (inj_head_nat ? ? ? ? H7);
                    rewrite < Hletin3 in H6;rewrite > H6 in H4;
                    apply (Hletin1 H4)
                   |intros;lapply (inj_tail ? ? ? ? ? H9);
                    rewrite < Hletin3 in H6;rewrite < H8 in H6;
                    apply (H1 ? H4 H6)]]]
          |elim (leb a s);auto]]]]
qed.

(*** lemmas on well-formedness ***)

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
           
lemma WFE_consG_to_WFT : \forall G.\forall b,X,T.
                         (WFEnv ((mk_bound b X T)::G)) \to (WFType G T).
intros.
inversion H
  [intro;reduce in H1;destruct H1
  |intros;lapply (inj_head ? ? ? ? H5);lapply (inj_tail ? ? ? ? ? H5);
   destruct Hletin;rewrite > Hletin1;rewrite > Hcut2;assumption]
qed.
         
lemma WFE_consG_WFE_G : \forall G.\forall b.
                         (WFEnv (b::G)) \to (WFEnv G).
intros.
inversion H
  [intro;reduce in H1;destruct H1
  |intros;lapply (inj_tail ? ? ? ? ? H5);rewrite > Hletin;assumption]
qed.

lemma WFT_swap : \forall u,v,G,T.(WFType G T) \to
                    (WFType (swap_Env u v G) (swap_Typ u v T)).
intros.elim H
  [simplify;apply WFT_TFree;lapply (natinfv_boundinenv ? ? H1);elim Hletin;
   elim H2;apply boundinenv_natinfv;apply ex_intro
     [apply a
     |apply ex_intro 
        [apply (swap_Typ u v a1)
        |apply lookup_swap;assumption]]
  |simplify;apply WFT_Top
  |simplify;apply WFT_Arrow
     [assumption|assumption]
  |simplify;apply WFT_Forall
     [assumption
     |intros;rewrite < (swap_inv u v);
      cut (\lnot (in_list ? (swap u v X) (fv_type t1)))
        [cut (\lnot (in_list ? (swap u v X) (fv_env e)))
           [generalize in match (H4 ? Hcut1 Hcut);simplify;
            rewrite > subst_type_O_swap;intro;assumption
           |lapply (in_dom_swap u v (swap u v X) e);elim Hletin;unfold;
            intros;lapply (H7 H9);rewrite > (swap_inv u v) in Hletin1;
            apply (H5 Hletin1)] 
        |generalize in match (in_fv_type_swap u v (swap u v X) t1);intros;
         elim H7;unfold;intro;lapply (H8 H10);
         rewrite > (swap_inv u v) in Hletin;apply (H6 Hletin)]]]
qed.

lemma WFE_swap : \forall u,v,G.(WFEnv G) \to (WFEnv (swap_Env u v G)).
intros 3.elim G 0
  [intro;simplify;assumption
  |intros 2;elim s;simplify;constructor 2
     [apply H;apply (WFE_consG_WFE_G ? ? H1)
     |unfold;intro;lapply (in_dom_swap u v n l);elim Hletin;lapply (H4 H2);
      (* FIXME trick *)generalize in match H1;intro;inversion H1
        [intros;absurd ((mk_bound b n t)::l = [])
           [assumption|apply nil_cons]
        |intros;lapply (inj_head ? ? ? ? H10);lapply (inj_tail ? ? ? ? ? H10);
         destruct Hletin2;rewrite < Hcut1 in H8;rewrite < Hletin3 in H8;
         apply (H8 Hletin1)]
     |apply (WFT_swap u v l t);inversion H1
        [intro;absurd ((mk_bound b n t)::l = [])
           [assumption|apply nil_cons]
        |intros;lapply (inj_head ? ? ? ? H6);lapply (inj_tail ? ? ? ? ? H6);
         destruct Hletin;rewrite > Hletin1;rewrite > Hcut2;assumption]]]
qed.

(*** some exotic inductions and related lemmas ***) 
(* FIXME : use nat_elim1 instead *)

lemma nat_ind_strong: \forall P:nat \to Prop.
                      (P O) \to
                      (\forall m.(\forall n.(n < m) \to (P n)) \to (P m)) \to
                      \forall n.(P n).
cut (\forall P:nat \to Prop.\forall n.
       (P O) \to (\forall m.(P m) \to (P (S m))) \to (P n))
  [intros;cut ((\lambda l.\forall m.(m < (S l)) \to (P m)) n)
     [simplify in Hcut1;apply Hcut1;unfold;constructor 1
     |cut (\forall m:nat.(m < (S O)) \to (P m))
        [cut (\forall n.
                ((\lambda l.\forall m.(m < (S l)) \to (P m)) n) \to
                ((\lambda l.\forall m.(m < (S l)) \to (P m)) (S n)))
           [apply (Hcut ? ? Hcut1 Hcut2)
           |simplify;intros 2;lapply (H1 ? H2);intros;unfold in H3;
            lapply (le_S_S_to_le ? ? H3);
            lapply (le_to_or_lt_eq ? ? Hletin1);
            elim Hletin2
              [apply (H2 ? H4)
              |rewrite > H4;assumption]]
        |intros;unfold in H2;lapply (le_S_S_to_le ? ? H2);
         generalize in match Hletin;elim m
           [assumption
           |absurd ((S n1) \leq O)
              [assumption|apply not_le_Sn_O]]]]
  |intros 2;elim n
     [assumption
     |apply (H2 ? (H H1 H2))]]
qed.

(* TODO : relocate the following 2 lemmas *)

lemma max_case : \forall m,n.(max m n) = match (leb m n) with
      [ false \Rightarrow n
      | true \Rightarrow m ].
intros;elim m;simplify;reflexivity;
qed.

lemma not_t_len_lt_SO : \forall T.\lnot (t_len T) < (S O).
intros;elim T
  [simplify;unfold;intro;unfold in H;elim (not_le_Sn_n ? H)
  |simplify;unfold;intro;unfold in H;elim (not_le_Sn_n ? H)
  |simplify;unfold;intro;unfold in H;elim (not_le_Sn_n ? H)
  |simplify;unfold;rewrite > max_case;elim (leb (t_len t) (t_len t1))
     [simplify in H2;apply H1;apply (trans_lt ? ? ? ? H2);unfold;constructor 1
     |simplify in H2;apply H;apply (trans_lt ? ? ? ? H2);unfold;constructor 1]
  |simplify;unfold;rewrite > max_case;elim (leb (t_len t) (t_len t1))
     [simplify in H2;apply H1;apply (trans_lt ? ? ? ? H2);unfold;constructor 1
     |simplify in H2;apply H;apply (trans_lt ? ? ? ? H2);unfold;constructor 1]]
qed.

lemma t_len_gt_O : \forall T.(t_len T) > O.
intro;elim T
  [simplify;unfold;unfold;constructor 1
  |simplify;unfold;unfold;constructor 1
  |simplify;unfold;unfold;constructor 1
  |simplify;lapply (max_case (t_len t) (t_len t1));rewrite > Hletin;
   elim (leb (t_len t) (t_len t1))
     [simplify;unfold;unfold;constructor 2;unfold in H1;unfold in H1;assumption
     |simplify;unfold;unfold;constructor 2;unfold in H;unfold in H;assumption]
  |simplify;lapply (max_case (t_len t) (t_len t1));rewrite > Hletin;
   elim (leb (t_len t) (t_len t1))
     [simplify;unfold;unfold;constructor 2;unfold in H1;unfold in H1;assumption
     |simplify;unfold;unfold;constructor 2;unfold in H;unfold in H;assumption]]
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
     [apply H;intros;simplify in H4;elim (not_t_len_lt_SO ? H4)
     |apply H;intros;simplify in H4;elim (not_t_len_lt_SO ? H4)
     |apply H;intros;simplify in H4;elim (not_t_len_lt_SO ? H4)
     |apply H;intros;apply (H1 (t_len V))
        [rewrite > H5;assumption
        |reflexivity]
     |apply H;intros;apply (H1 (t_len V))
        [rewrite > H5;assumption
        |reflexivity]]]
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
     |elim (leb (t_len T1) (t_len T2));auto]
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
     |elim (leb (t_len T1) (t_len T2));auto]
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
     |elim (leb (t_len T1) (t_len T2));auto]
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
     |elim (leb (t_len T1) (t_len T2));auto]
  |elim T1;simplify;reflexivity]
qed.

lemma eq_t_len_TFree_subst : \forall T,n,X.(t_len T) = 
                                         (t_len (subst_type_nat T (TFree X) n)).
intro.elim T
  [simplify;elim (eqb n n1)
     [simplify;reflexivity
     |simplify;reflexivity]
  |simplify;reflexivity
  |simplify;reflexivity
  |simplify;lapply (H n X);lapply (H1 n X);rewrite < Hletin;rewrite < Hletin1;
   reflexivity
  |simplify;lapply (H n X);lapply (H1 (S n) X);rewrite < Hletin;
   rewrite < Hletin1;reflexivity]
qed.

lemma swap_env_not_free : \forall u,v,G.(WFEnv G) \to 
                                        \lnot (in_list ? u (fv_env G)) \to
                                        \lnot (in_list ? v (fv_env G)) \to
                                        (swap_Env u v G) = G.
intros 3.elim G 0
  [simplify;intros;reflexivity
  |intros 2;elim s 0;simplify;intros;lapply (notin_cons ? ? ? ? H2);
   lapply (notin_cons ? ? ? ? H3);elim Hletin;elim Hletin1;
   lapply (swap_other ? ? ? H4 H6);lapply (WFE_consG_to_WFT ? ? ? ? H1);
   cut (\lnot (in_list ? u (fv_type t)))
     [cut (\lnot (in_list ? v (fv_type t)))
        [lapply (swap_Typ_not_free ? ? ? Hcut Hcut1);
         lapply (WFE_consG_WFE_G ? ? H1);
         lapply (H Hletin5 H5 H7);
         rewrite > Hletin2;rewrite > Hletin4;rewrite > Hletin6;reflexivity
        |unfold;intro;apply H7;
         apply (fv_WFT ? ? ? Hletin3 H8)] 
     |unfold;intro;apply H5;apply (fv_WFT ? ? ? Hletin3 H8)]]
qed.

(*** alternative "constructor" for universal types' well-formedness ***)

lemma WFT_Forall2 : \forall G,X,T,T1,T2.
                       (WFEnv G) \to
                       (WFType G T1) \to
                       \lnot (in_list ? X (fv_type T2)) \to
                       \lnot (in_list ? X (fv_env G)) \to
                       (WFType ((mk_bound true X T)::G) 
                          (subst_type_O T2 (TFree X))) \to
                    (WFType G (Forall T1 T2)).
intros.apply WFT_Forall
  [assumption
  |intros;generalize in match (WFT_swap X X1 ? ? H4);simplify;
   rewrite > swap_left;
   rewrite > (swap_env_not_free X X1 G H H3 H5);
   rewrite > subst_type_O_swap;rewrite > swap_left;
   rewrite > (swap_Typ_not_free ? ? T2 H2 H6);
   intro;apply (WFT_env_incl ? ? H7);unfold;simplify;intros;assumption]
qed.

(*** lemmas relating subtyping and well-formedness ***)

lemma JS_to_WFE : \forall G,T,U.(JSubtype G T U) \to (WFEnv G).
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
     [lapply (fresh_name ((fv_env e) @ (fv_type t1)));
      elim Hletin;cut ((\lnot (in_list ? a (fv_env e))) \land
                       (\lnot (in_list ? a (fv_type t1))))
        [elim Hcut;apply (WFT_Forall2 ? a t2 ? ? (JS_to_WFE ? ? ? H1) H6 H9 H8);
         lapply (H4 ? H8);elim Hletin1;assumption
        |split;unfold;intro;apply H7;apply natinG_or_inH_to_natinGH
           [right;assumption
           |left;assumption]]
     |lapply (fresh_name ((fv_env e) @ (fv_type t3)));
      elim Hletin;cut ((\lnot (in_list ? a (fv_env e))) \land
                       (\lnot (in_list ? a (fv_type t3))))
        [elim Hcut;apply (WFT_Forall2 ? a t2 ? ? (JS_to_WFE ? ? ? H1) H5 H9 H8);
         lapply (H4 ? H8);elim Hletin1;assumption
        |split;unfold;intro;apply H7;apply natinG_or_inH_to_natinGH
           [right;assumption
           |left;assumption]]]]
qed.

lemma JS_to_WFT1 : \forall G,T,U.(JSubtype G T U) \to (WFType G T).
intros;lapply (JS_to_WFT ? ? ? H);elim Hletin;assumption.
qed.

lemma JS_to_WFT2 : \forall G,T,U.(JSubtype G T U) \to (WFType G U).
intros;lapply (JS_to_WFT ? ? ? H);elim Hletin;assumption.
qed.

(*** lemma relating subtyping and swaps ***)

lemma JS_swap : \forall u,v,G,T,U.(JSubtype G T U) \to
                   (JSubtype (swap_Env u v G) (swap_Typ u v T) (swap_Typ u v U)).
intros 6.elim H
  [simplify;apply SA_Top
     [apply WFE_swap;assumption
     |apply WFT_swap;assumption]
  |simplify;apply SA_Refl_TVar
     [apply WFE_swap;assumption
     |unfold in H2;unfold;lapply (in_dom_swap u v n e);elim Hletin;
      apply (H3 H2)]
  |simplify;apply SA_Trans_TVar
     [apply (swap_Typ u v t1)
     |apply lookup_swap;assumption
     |assumption]
  |simplify;apply SA_Arrow;assumption
  |simplify;apply SA_All
     [assumption
     |intros;lapply (H4 (swap u v X))
        [simplify in Hletin;rewrite > subst_type_O_swap in Hletin;
         rewrite > subst_type_O_swap in Hletin;rewrite > swap_inv in Hletin;
         assumption
        |unfold;intro;apply H5;unfold;
         lapply (in_dom_swap u v (swap u v X) e);
         elim Hletin;rewrite > swap_inv in H7;apply H7;assumption]]]
qed.

lemma fresh_WFT : \forall x,G,T.(WFType G T) \to \lnot (in_list ? x (fv_env G))
                     \to \lnot (in_list ? x (fv_type T)).
intros;unfold;intro;apply H1;apply (fv_WFT ? ? ? H H2);
qed.

lemma fresh_subst_type_O : \forall x,T1,B,G,T,y.
                  (WFType ((mk_bound B x T1)::G) (subst_type_O T (TFree x))) \to
                  \lnot (in_list ? y (fv_env G)) \to (x \neq y) \to
                  \lnot (in_list ? y (fv_type T)).
intros;unfold;intro;
cut (in_list ? y (fv_env ((mk_bound B x T1) :: G)))
  [simplify in Hcut;inversion Hcut
     [intros;apply H2;lapply (inj_head_nat ? ? ? ? H5);rewrite < H4 in Hletin;
      assumption
     |intros;apply H1;rewrite > H6;lapply (inj_tail ? ? ? ? ? H7);
      rewrite > Hletin;assumption]
  |apply (fv_WFT (subst_type_O T (TFree x)) ? ? H);
   apply fv_subst_type_O;assumption]
qed.

(*** alternative "constructor" for subtyping between universal types ***)

lemma SA_All2 : \forall G,S1,S2,T1,T2,X.(JSubtype G T1 S1) \to
                   \lnot (in_list ? X (fv_env G)) \to
                   \lnot (in_list ? X (fv_type S2)) \to
                   \lnot (in_list ? X (fv_type T2)) \to
                   (JSubtype ((mk_bound true X T1) :: G)
                      (subst_type_O S2 (TFree X))
                      (subst_type_O T2 (TFree X))) \to
                   (JSubtype G (Forall S1 S2) (Forall T1 T2)).
intros;apply (SA_All ? ? ? ? ? H);intros;
lapply (decidable_eq_nat X X1);elim Hletin
  [rewrite < H6;assumption
  |elim (JS_to_WFT ? ? ? H);elim (JS_to_WFT ? ? ? H4);
   cut (\lnot (in_list ? X1 (fv_type S2)))
     [cut (\lnot (in_list ? X1 (fv_type T2)))
        [cut (((mk_bound true X1 T1)::G) =
              (swap_Env X X1 ((mk_bound true X T1)::G)))
           [rewrite > Hcut2;
            cut (((subst_type_O S2 (TFree X1)) =
                   (swap_Typ X X1 (subst_type_O S2 (TFree X)))) \land
                 ((subst_type_O T2 (TFree X1)) =
                   (swap_Typ X X1 (subst_type_O T2 (TFree X)))))
              [elim Hcut3;rewrite > H11;rewrite > H12;apply JS_swap;
               assumption
              |split
                 [rewrite > (subst_type_O_swap X X1 S2 X);
                  rewrite > (swap_Typ_not_free X X1 S2 H2 Hcut); 
                  rewrite > swap_left;reflexivity
                 |rewrite > (subst_type_O_swap X X1 T2 X);
                  rewrite > (swap_Typ_not_free X X1 T2 H3 Hcut1); 
                  rewrite > swap_left;reflexivity]]
           |simplify;lapply (JS_to_WFE ? ? ? H);
            rewrite > (swap_env_not_free X X1 G Hletin1 H1 H5);
            cut ((\lnot (in_list ? X (fv_type T1))) \land
                 (\lnot (in_list ? X1 (fv_type T1))))
              [elim Hcut2;rewrite > (swap_Typ_not_free X X1 T1 H11 H12);
               rewrite > swap_left;reflexivity
              |split
                 [unfold;intro;apply H1;apply (fv_WFT T1 X G H7 H11)
                 |unfold;intro;apply H5;apply (fv_WFT T1 X1 G H7 H11)]]]
        |unfold;intro;apply H5;lapply (fv_WFT ? X1 ? H10)
           [inversion Hletin1
              [intros;simplify in H13;lapply (inj_head_nat ? ? ? ? H13);
               rewrite < H12 in Hletin2;lapply (H6 Hletin2);elim Hletin3
              |intros;simplify in H15;lapply (inj_tail ? ? ? ? ? H15);
               rewrite < Hletin2 in H12;rewrite < H14 in H12;lapply (H5 H12);
               elim Hletin3]
           |rewrite > subst_O_nat;apply in_FV_subst;assumption]]
     |unfold;intro;apply H5;lapply (fv_WFT ? X1 ? H9)
        [inversion Hletin1
           [intros;simplify in H13;lapply (inj_head_nat ? ? ? ? H13);
            rewrite < H12 in Hletin2;lapply (H6 Hletin2);elim Hletin3
           |intros;simplify in H15;lapply (inj_tail ? ? ? ? ? H15);
            rewrite < Hletin2 in H12;rewrite < H14 in H12;lapply (H5 H12);
            elim Hletin3]
        |rewrite > subst_O_nat;apply in_FV_subst;assumption]]]
qed.
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
include "Fsub/util.ma".

(*** representation of Fsub types ***)  
inductive Typ : Set \def
  | TVar : nat \to Typ            (* type var *)
  | TFree: nat \to Typ            (* free type name *)
  | Top : Typ                     (* maximum type *)
  | Arrow : Typ \to Typ \to Typ   (* functions *) 
  | Forall : Typ \to Typ \to Typ. (* universal type *)

(* representation of bounds *)

record bound : Set \def { 
                          istype : bool;    (* is subtyping bound? *)
                          name   : nat ;    (* name *)
                          btype  : Typ      (* type to which the name is bound *)
                        }.
               
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

(*** height of T's syntactic tree ***)

let rec t_len T \def
  match T with
     [(TVar n) \Rightarrow (S O)
     |(TFree X) \Rightarrow (S O)
     |Top \Rightarrow (S O)
     |(Arrow T1 T2) \Rightarrow (S (max (t_len T1) (t_len T2)))
     |(Forall T1 T2) \Rightarrow (S (max (t_len T1) (t_len T2)))].

(*** definitions about lists ***)

definition fv_env : (list bound) \to (list nat) \def
  \lambda G.(map ? ? (\lambda b.match b with
      [(mk_bound B X T) \Rightarrow X]) G).

let rec fv_type T \def
  match T with
    [(TVar n) \Rightarrow []
    |(TFree x) \Rightarrow [x]
    |Top \Rightarrow []
    |(Arrow U V) \Rightarrow ((fv_type U) @ (fv_type V))
    |(Forall U V) \Rightarrow ((fv_type U) @ (fv_type V))].

(*** Type Well-Formedness judgement ***)

inductive WFType : (list bound) \to Typ \to Prop \def
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
                       (subst_type_nat U (TFree X) O))) \to 
                 (WFType G (Forall T U)).

(*** Environment Well-Formedness judgement ***)

inductive WFEnv : (list bound) \to Prop \def
  | WFE_Empty : (WFEnv (nil ?))
  | WFE_cons : \forall B,X,T,G.(WFEnv G) \to 
               \lnot (in_list ? X (fv_env G)) \to
                  (WFType G T) \to (WFEnv ((mk_bound B X T) :: G)).
            
(*** Subtyping judgement ***)              
inductive JSubtype : (list bound) \to Typ \to Typ \to Prop \def
  | SA_Top : \forall G.\forall T:Typ.(WFEnv G) \to
             (WFType G T) \to (JSubtype G T Top)
  | SA_Refl_TVar : \forall G.\forall X:nat.(WFEnv G) 
                   \to (in_list ? X (fv_env G)) 
                   \to (JSubtype G (TFree X) (TFree X))
  | SA_Trans_TVar : \forall G.\forall X:nat.\forall T:Typ.
                    \forall U:Typ.
                    (in_list ? (mk_bound true X U) G) \to
                    (JSubtype G U T) \to (JSubtype G (TFree X) T)
  | SA_Arrow : \forall G.\forall S1,S2,T1,T2:Typ.
               (JSubtype G T1 S1) \to (JSubtype G S2 T2) \to
               (JSubtype G (Arrow S1 S2) (Arrow T1 T2))
  | SA_All : \forall G.\forall S1,S2,T1,T2:Typ.
             (JSubtype G T1 S1) \to
             (\forall X:nat.\lnot (in_list ? X (fv_env G)) \to
                (JSubtype ((mk_bound true X T1) :: G) 
                   (subst_type_nat S2 (TFree X) O) (subst_type_nat T2 (TFree X) O))) \to
             (JSubtype G (Forall S1 S2) (Forall T1 T2)).

notation "hvbox(e ⊢ break ta ⊴  break tb)" 
  non associative with precedence 30 for @{ 'subjudg $e $ta $tb }.  
interpretation "Fsub subtype judgement" 'subjudg e ta tb =
 (cic:/matita/Fsub/defn/JSubtype.ind#xpointer(1/1) e ta tb).

notation > "hvbox(\Forall S.T)" 
  non associative with precedence 60 for @{ 'forall $S $T}.
notation < "hvbox('All' \sub S. break T)" 
  non associative with precedence 60 for @{ 'forall $S $T}.
interpretation "universal type" 'forall S T = 
  (cic:/matita/Fsub/defn/Typ.ind#xpointer(1/1/5) S T).
  
notation "#x" with precedence 79 for @{'tvar $x}.
interpretation "bound tvar" 'tvar x = 
  (cic:/matita/Fsub/defn/Typ.ind#xpointer(1/1/1) x).

notation "!x" with precedence 79 for @{'tname $x}.
interpretation "bound tname" 'tname x = 
  (cic:/matita/Fsub/defn/Typ.ind#xpointer(1/1/2) x).
  
notation "⊤" with precedence 90 for @{'toptype}.
interpretation "toptype" 'toptype = 
  (cic:/matita/Fsub/defn/Typ.ind#xpointer(1/1/3)).

notation "hvbox(s break ⇛ t)"
  right associative with precedence 55 for @{ 'arrow $s $t }.
interpretation "arrow type" 'arrow S T = 
  (cic:/matita/Fsub/defn/Typ.ind#xpointer(1/1/4) S T).
  
notation "hvbox(S [# n ↦ T])"
  non associative with precedence 80 for @{ 'substvar $S $T $n }.
interpretation "subst bound var" 'substvar S T n =
  (cic:/matita/Fsub/defn/subst_type_nat.con S T n).  

notation "hvbox(|T|)"
  non associative with precedence 30 for @{ 'tlen $T }.
interpretation "type length" 'tlen T =
  (cic:/matita/Fsub/defn/t_len.con T).  

notation "hvbox(!X ⊴ T)"
  non associative with precedence 60 for @{ 'subtypebound $X $T }.
interpretation "subtyping bound" 'subtypebound X T =
  (cic:/matita/Fsub/defn/bound.ind#xpointer(1/1/1) true X T).  

(****** PROOFS ********)

(*** theorems about lists ***)

lemma boundinenv_natinfv : \forall x,G.
                              (\exists B,T.(in_list ? (mk_bound B x T) G)) \to
                              (in_list ? x (fv_env G)).
intros 2;elim G
  [elim H;elim H1;lapply (in_list_nil ? ? H2);elim Hletin
  |elim H1;elim H2;elim (in_cons_case ? ? ? ? H3)
     [rewrite < H4;simplify;apply in_Base
     |elim H4;elim t;simplify;apply in_Skip2;apply H;apply (ex_intro ? ? a);
      apply (ex_intro ? ? a1);assumption]]
qed.

lemma nat_in_list_case : \forall G,H,n.(in_list nat n (H @ G)) \to 
                               (in_list nat n G) \lor (in_list nat n H).
intros 3.elim H
  [simplify in H1;left;assumption
  |simplify in H2;elim (in_cons_case ? ? ? ? H2)
    [right;rewrite > H3;apply in_Base
    |elim H3;elim (H1 H5) [left;assumption|right;apply in_Skip2;assumption]]]
qed.

lemma natinG_or_inH_to_natinGH : \forall G,H,n.
                      (in_list nat n G) \lor (in_list nat n H) \to
                      (in_list nat n (H @ G)).
intros.elim H1
  [elim H
     [simplify;assumption
     |simplify;apply in_Skip2;assumption]
  |generalize in match H2;elim H2
     [simplify;apply in_Base
     |lapply (H4 H3);simplify;apply in_Skip;assumption]]
qed.

lemma natinfv_boundinenv : \forall x,G.(in_list ? x (fv_env G)) \to
                              \exists B,T.(in_list ? (mk_bound B x T) G).
intros 2;elim G 0
  [simplify;intro;lapply (in_list_nil ? ? H);elim Hletin
  |intros 3;elim t;simplify in H1;elim (in_cons_case ? ? ? ? H1)
     [rewrite < H2;apply (ex_intro ? ? b);apply (ex_intro ? ? t1);apply in_Base
     |elim H2;elim (H H4);elim H5;apply (ex_intro ? ? a);
      apply (ex_intro ? ? a1);apply in_Skip
        [assumption
        |intro;destruct H7;elim (H3 Hcut1)]]]
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
intros.unfold in H.unfold.intros.elim (in_cons_case ? ? ? ? H1)
  [rewrite > H2;apply in_Base|elim H2;apply in_Skip2;apply (H ? H4)]
qed.

lemma WFT_env_incl : \forall G,T.(WFType G T) \to
                     \forall H.(incl ? (fv_env G) (fv_env H)) \to (WFType H T).
intros 3.elim H
  [apply WFT_TFree;unfold in H3;apply (H3 ? H1)
  |apply WFT_Top
  |apply WFT_Arrow [apply (H2 ? H6)|apply (H4 ? H6)]
  |apply WFT_Forall 
     [apply (H2 ? H6)
     |intros;apply (H4 ? ? H8)
        [unfold;intro;apply H7;apply(H6 ? H9)
        |simplify;apply (incl_nat_cons ? ? ? H6)]]]
qed.

lemma fv_env_extends : \forall H,x,B,C,T,U,G.
                          (fv_env (H @ ((mk_bound B x T) :: G))) = 
                          (fv_env (H @ ((mk_bound C x U) :: G))).
intros;elim H
  [simplify;reflexivity|elim t;simplify;rewrite > H1;reflexivity]
qed.

lemma lookup_env_extends : \forall G,H,B,C,D,T,U,V,x,y.
            (in_list ? (mk_bound D y V) (H @ ((mk_bound C x U) :: G))) \to
            (y \neq x) \to
            (in_list ? (mk_bound D y V) (H @ ((mk_bound B x T) :: G))).
intros 10;elim H
  [simplify in H1;elim (in_cons_case ? ? ? ? H1)
     [destruct H3;elim (H2 Hcut1)
     |simplify;elim H3;apply (in_Skip ? ? ? ? H5);intro;destruct H6;
      apply (H2 Hcut1)] 
  |simplify in H2;simplify;elim (in_cons_case ? ? ? ? H2)
     [rewrite > H4;apply in_Base
     |elim H4;apply (in_Skip ? ? ? ? (H1 H6 H3) H5)]]
qed.

lemma in_FV_subst : \forall x,T,U,n.(in_list ? x (fv_type T)) \to
                                (in_list ? x (fv_type (subst_type_nat T U n))).
intros 3;elim T
  [simplify in H;elim (in_list_nil ? ? H)
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
    [apply (ex_intro ? ? O);intros;unfold;intro;elim (in_list_nil ? ? H1)
    |elim H;elim (decidable_eq_nat a t)
       [apply (ex_intro ? ? (S a));intros;intro;elim (in_cons_case ? ? ? ? H4)
          [rewrite < H5 in H2;rewrite < H2 in H3;apply (not_le_Sn_n ? H3)
          |elim H5;elim (H1 m ? H7);apply (le_S_S_to_le ? ? (le_S ? ? H3))]
       |cut ((leb a t) = true \lor (leb a t) = false)
          [elim Hcut
             [apply (ex_intro ? ? (S t));intros;intro;
              elim (in_cons_case ? ? ? ? H5)
                [rewrite > H6 in H4;apply (not_le_Sn_n ? H4)
                |elim H6;elim (H1 m ? H8);apply (trans_le a t m)
                   [lapply (leb_to_Prop a t);rewrite > H3 in Hletin;assumption
                   |apply (le_S_S_to_le t m (le_S (S t) m H4))]]
             |apply (ex_intro ? ? a);intros;intro;elim (in_cons_case ? ? ? ? H5)
                [lapply (leb_to_Prop a t);rewrite > H3 in Hletin;
                 simplify in Hletin;lapply (not_le_to_lt ? ? Hletin);
                 unfold in Hletin1;rewrite < H6 in Hletin;apply (Hletin H4)
                |elim H6;elim (H1 ? H4 H8)]]
          |elim (leb a t);autobatch]]]]
qed.

(*** lemmata on well-formedness ***)

lemma fv_WFT : \forall T,x,G.(WFType G T) \to (in_list ? x (fv_type T)) \to
                  (in_list ? x (fv_env G)).
intros 4.elim H
  [simplify in H2;elim (in_cons_case ? ? ? ? H2)
     [rewrite > H3;assumption|elim H3;elim (in_list_nil ? ? H5)]
  |simplify in H1;elim (in_list_nil ? x H1)
  |simplify in H5;elim (nat_in_list_case ? ? ? H5);autobatch
  |simplify in H5;elim (nat_in_list_case ? ? ? H5)
     [elim (fresh_name ((fv_type t1) @ (fv_env l)));
      cut ((¬ (in_list ? a (fv_type t1))) ∧
           (¬ (in_list ? a (fv_env l))))
        [elim Hcut;lapply (H4 ? H9 H8)
           [cut (x ≠ a)
              [simplify in Hletin;elim (in_cons_case ? ? ? ? Hletin)
                 [elim (Hcut1 H10)|elim H10;assumption]
              |intro;apply H8;rewrite < H10;assumption]
           |apply in_FV_subst;assumption]
        |split
           [intro;apply H7;apply natinG_or_inH_to_natinGH;right;assumption
           |intro;apply H7;apply natinG_or_inH_to_natinGH;left;assumption]]
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
      [ false ⇒ (t_len T2)
      | true  ⇒ (t_len T1) ])
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

lemma JS_to_WFE : \forall G,T,U.(G \vdash T ⊴ U) \to (WFEnv G).
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
  [simplify;intros;(*FIXME*)generalize in match H1;intro;inversion H1;intros
     [lapply (nil_cons ? G (mk_bound B x T));elim (Hletin H4)
     |destruct H8;rewrite < Hcut2 in H6;rewrite < Hcut in H4;
      rewrite < Hcut in H6;apply (WFE_cons ? ? ? ? H4 H6 H2)]
  |intros;simplify;generalize in match H2;elim t;simplify in H4;
   inversion H4;intros
     [destruct H5
     |destruct H9;apply WFE_cons
        [rewrite < Hcut in H5;apply (H1 H5 H3)
        |rewrite < (fv_env_extends ? x B C T U);rewrite > Hcut;rewrite > Hcut2;
         assumption
        |rewrite < Hcut3 in H8;rewrite > Hcut1;apply (WFT_env_incl ? ? H8);
         rewrite < (fv_env_extends ? x B C T U);unfold;intros;
         rewrite > Hcut;assumption]]]
qed.

lemma WFE_bound_bound : \forall B,x,T,U,G. (WFEnv G) \to
                                  (in_list ? (mk_bound B x T) G) \to
                                  (in_list ? (mk_bound B x U) G) \to T = U.
intros 6;elim H
  [lapply (in_list_nil ? ? H1);elim Hletin
  |elim (in_cons_case ? ? ? ? H6)
     [destruct H7;subst;elim (in_cons_case ? ? ? ? H5)
        [destruct H7;assumption
        |elim H7;elim H3;apply boundinenv_natinfv;apply (ex_intro ? ? b);
         apply (ex_intro ? ? T);assumption]
     |elim H7;elim (in_cons_case ? ? ? ? H5)
        [destruct H10;elim H3;apply boundinenv_natinfv;apply (ex_intro ? ? B);
         apply (ex_intro ? ? U);rewrite < Hcut1;assumption
        |elim H10;apply (H2 H12 H9)]]]
qed.

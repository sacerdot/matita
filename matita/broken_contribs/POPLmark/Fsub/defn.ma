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

include "Fsub/util.ma".

(*** representation of Fsub types ***)  
inductive Typ : Set ≝
  | TVar : nat → Typ            (* type var *)
  | TFree: nat → Typ            (* free type name *)
  | Top : Typ                     (* maximum type *)
  | Arrow : Typ → Typ → Typ   (* functions *) 
  | Forall : Typ → Typ → Typ. (* universal type *)

(* representation of bounds *)

record bound : Set ≝ { 
                          istype : bool;    (* is subtyping bound? *)
                          name   : nat ;    (* name *)
                          btype  : Typ      (* type to which the name is bound *)
                        }.
               
(*** Various kinds of substitution, not all will be used probably ***)

(* substitutes i-th dangling index in type T with type U *)
let rec subst_type_nat T U i ≝
    match T with
    [ TVar n ⇒ match eqb n i with
      [ true ⇒ U
      | false ⇒ T]
    | TFree X ⇒ T
    | Top ⇒ T
    | Arrow T1 T2 ⇒ Arrow (subst_type_nat T1 U i) (subst_type_nat T2 U i)
    | Forall T1 T2 ⇒ Forall (subst_type_nat T1 U i) (subst_type_nat T2 U (S i)) ].

(*** definitions about lists ***)

definition filter_types : list bound → list bound ≝
  λG.(filter ? G (λB.match B with [mk_bound B X T ⇒ B])).

definition fv_env : list bound → list nat ≝
  λG.(map ? ? (λb.match b with [mk_bound B X T ⇒ X]) (filter_types G)).

let rec fv_type T ≝
  match T with
    [TVar n ⇒ []
    |TFree x ⇒ [x]
    |Top ⇒ []
    |Arrow U V ⇒ fv_type U @ fv_type V
    |Forall U V ⇒ fv_type U @ fv_type V].

(*** Type Well-Formedness judgement ***)

inductive WFType : list bound → Typ → Prop ≝
  | WFT_TFree : ∀X,G.in_list ? X (fv_env G) → WFType G (TFree X)
  | WFT_Top : ∀G.WFType G Top
  | WFT_Arrow : ∀G,T,U.WFType G T → WFType G U → WFType G (Arrow T U)
  | WFT_Forall : ∀G,T,U.WFType G T →
                   (∀X:nat.
                    (¬ (in_list ? X (fv_env G))) →
                    (¬ (in_list ? X (fv_type U))) →
                    (WFType ((mk_bound true X T) :: G)
                     (subst_type_nat U (TFree X) O))) → 
                 (WFType G (Forall T U)).

(*** Environment Well-Formedness judgement ***)

inductive WFEnv : list bound → Prop ≝
  | WFE_Empty : WFEnv (nil ?)
  | WFE_cons : ∀B,X,T,G.WFEnv G → ¬ (in_list ? X (fv_env G)) →
                  WFType G T → WFEnv ((mk_bound B X T) :: G).
            
(*** Subtyping judgement ***)              
inductive JSubtype : list bound → Typ → Typ → Prop ≝
  | SA_Top : ∀G,T.WFEnv G → WFType G T → JSubtype G T Top
  | SA_Refl_TVar : ∀G,X.WFEnv G → in_list ? X (fv_env G) 
                   → JSubtype G (TFree X) (TFree X)
  | SA_Trans_TVar : ∀G,X,T,U.in_list ? (mk_bound true X U) G →
                    JSubtype G U T → JSubtype G (TFree X) T
  | SA_Arrow : ∀G,S1,S2,T1,T2. JSubtype G T1 S1 → JSubtype G S2 T2 → 
               JSubtype G (Arrow S1 S2) (Arrow T1 T2)
  | SA_All : ∀G,S1,S2,T1,T2. JSubtype G T1 S1 →
             (∀X.¬ (in_list ? X (fv_env G)) →
               JSubtype ((mk_bound true X T1) :: G) 
                (subst_type_nat S2 (TFree X) O) (subst_type_nat T2 (TFree X) O)) →
             JSubtype G (Forall S1 S2) (Forall T1 T2).

notation "mstyle color #007f00 (hvbox(e ⊢ break ta ⊴ break tb))" 
  non associative with precedence 30 for @{ 'subjudg $e $ta $tb }.  
interpretation "Fsub subtype judgement" 'subjudg e ta tb = (JSubtype e ta tb).

notation "mstyle color #007f00 (hvbox(e ⊢ ♦))" 
  non associative with precedence 30 for @{ 'wfejudg $e }.  
interpretation "Fsub WF env judgement" 'wfejudg e = (WFEnv e).

notation "mstyle color #007f00 (hvbox(e ⊢ break t))" 
  non associative with precedence 30 for @{ 'wftjudg $e $t }.  
interpretation "Fsub WF type judgement" 'wftjudg e t = (WFType e t).

notation > "\Forall S.T" 
  non associative with precedence 65 for @{ 'forall $S $T}.
notation < "hvbox(⊓ \sub S. break T)" 
  non associative with precedence 65 for @{ 'forall $S $T}.
interpretation "universal type" 'forall S T = (Forall S T).
  
notation "#x" with precedence 79 for @{'tvar $x}.
interpretation "bound tvar" 'tvar x = (TVar x).

notation "!x" with precedence 79 for @{'tname $x}.
interpretation "bound tname" 'tname x = (TFree x).
  
notation "⊤" with precedence 90 for @{'toptype}.
interpretation "toptype" 'toptype = Top.

notation "hvbox(s break ⇛ t)"
  right associative with precedence 60 for @{ 'arrow $s $t }.
interpretation "arrow type" 'arrow S T = (Arrow S T).
  
notation "hvbox(S [#n ↦ T])"
  non associative with precedence 80 for @{ 'substvar $S $T $n }.
interpretation "subst bound var" 'substvar S T n = (subst_type_nat S T n).  

notation "hvbox(!X ⊴ T)"
  non associative with precedence 65 for @{ 'subtypebound $X $T }.
interpretation "subtyping bound" 'subtypebound X T = (mk_bound true X T).  

(****** PROOFS ********)

(*** theorems about lists ***)

lemma boundinenv_natinfv : ∀x,G.(∃T.!x ⊴ T ∈ G) → x ∈ (fv_env G).
intros 2;elim G;decompose
  [elim (not_in_list_nil ? ? H1)
  |elim (in_list_cons_case ? ? ? ? H2)
     [rewrite < H1;simplify;apply in_list_head
     |elim a;apply (bool_elim ? b);intro;simplify;try apply in_list_cons;
      apply H;autobatch]]
qed.

lemma natinfv_boundinenv : ∀x,G.x ∈ (fv_env G) → ∃T.!x ⊴ T ∈ G.
intros 2;elim G 0
  [simplify;intro;lapply (not_in_list_nil ? ? H);elim Hletin
  |intros 3;
   elim a;simplify in H1;elim b in H1;simplify in H1
   [elim (in_list_cons_case ? ? ? ? H1)
     [rewrite < H2;autobatch
     |elim (H H2);autobatch]
   |elim (H H1);autobatch]]
qed.

lemma incl_bound_fv : ∀l1,l2.l1 ⊆ l2 → (fv_env l1) ⊆ (fv_env l2).
intros;unfold in H;unfold;intros;apply boundinenv_natinfv;
lapply (natinfv_boundinenv ? ? H1);decompose;autobatch depth=4;
qed.

lemma WFT_env_incl : ∀G,T.(G ⊢ T) → ∀H.fv_env G ⊆ fv_env H → (H ⊢ T).
intros 3.elim H
  [apply WFT_TFree;unfold in H3;apply (H3 ? H1)
  |apply WFT_Top
  |apply WFT_Arrow;autobatch
  |apply WFT_Forall 
     [apply (H2 ? H6)
     |intros;apply (H4 ? ? H8)
        [unfold;intro;autobatch
        |simplify;apply (incl_cons ???? H6)]]]
qed.

lemma fv_env_extends : ∀H,x,T,U,G,B.
                         fv_env (H @ mk_bound B x T :: G) = 
                         fv_env (H @ mk_bound B x U :: G).
intros 5;elim H;elim B
  [1,2:reflexivity
  |*:elim a;elim b;simplify;lapply (H1 true);lapply (H1 false);
   try rewrite > Hletin;try rewrite > Hletin1;reflexivity]
qed.

lemma lookup_env_extends : ∀G,H,B,C,D,T,U,V,x,y.
            mk_bound D y V ∈ H @ mk_bound C x U :: G → y ≠ x → 
            mk_bound D y V ∈ H @ mk_bound B x T :: G.
intros 10;elim H
  [simplify in H1;elim (in_list_cons_case ? ? ? ? H1)
     [destruct H3;elim H2;reflexivity
     |simplify;apply (in_list_cons ? ? ? ? H3);]
  |simplify in H2;simplify;elim (in_list_cons_case ? ? ? ? H2)
     [rewrite > H4;apply in_list_head
     |apply (in_list_cons ? ? ? ? (H1 H4 H3))]]
qed.

lemma in_FV_subst : ∀x,T,U,n.x ∈ fv_type T → x ∈ fv_type (subst_type_nat T U n).
intros 3;elim T
  [simplify in H;elim (not_in_list_nil ? ? H)
  |2,3:simplify;simplify in H;assumption
  |*:simplify in H2;simplify;elim (in_list_append_to_or_in_list ? ? ? ? H2);
     autobatch]
qed.

(*** lemma on fresh names ***)

lemma fresh_name : ∀l:list nat.∃n.n ∉ l.
cut (∀l:list nat.∃n.∀m.n ≤ m → ¬ in_list ? m l);intros
  [lapply (Hcut l);elim Hletin;apply ex_intro;autobatch
  |elim l
    [apply ex_intro[apply O];intros;unfold;intro;elim (not_in_list_nil ? ? H1)
    |elim H;apply ex_intro[apply (S (max a1 a))];
     intros;unfold;intro;
     elim (in_list_cons_case ? ? ? ? H3)
      [rewrite > H4 in H2;autobatch
      |elim H4
         [apply (H1 m ? H4);autobatch
         |assumption]]]]
qed.

(*** lemmata on well-formedness ***)

lemma fv_WFT : ∀T,x,G.(G ⊢ T) → x ∈ fv_type T → x ∈ fv_env G.
intros 4.elim H
  [simplify in H2;elim (in_list_cons_case ? ? ? ? H2)
     [applyS H1|elim (not_in_list_nil ? ? H3)]
  |simplify in H1;elim (not_in_list_nil ? x H1)
  |simplify in H5;elim (in_list_append_to_or_in_list ? ? ? ? H5);autobatch
  |simplify in H5;elim (in_list_append_to_or_in_list ? ? ? ? H5)
     [apply (H2 H6)
     |elim (fresh_name (fv_type t1 @ fv_env l));
      cut (¬ in_list ? a (fv_type t1) ∧ ¬ in_list ? a (fv_env l))
        [elim Hcut;lapply (H4 ? H9 H8)
           [cut (x ≠ a)
              [simplify in Hletin;elim (in_list_cons_case ? ? ? ? Hletin)
                 [elim (Hcut1 H10)
                 |assumption]
              |intro;apply H8;applyS H6]
           |autobatch]
        |split;intro;apply H7;autobatch]]]
qed.

(*** lemmata relating subtyping and well-formedness ***)

lemma JS_to_WFE : ∀G,T,U.G ⊢ T ⊴ U → G ⊢ ♦.
intros;elim H;assumption.
qed.

lemma JS_to_WFT : ∀G,T,U.G ⊢ T ⊴ U → (G ⊢ T) ∧ (G ⊢ U).
intros;elim H
  [1,2:autobatch
  |split 
    [apply WFT_TFree;(* FIXME! qui bastava autobatch, ma si e` rotto *) apply boundinenv_natinfv;autobatch 
    |elim H3;assumption]
  |decompose;autobatch size=7
  |elim H2;split
     [apply (WFT_Forall ? ? ? H6);intros;elim (H4 X H7);
      apply (WFT_env_incl ? ? H9);simplify;unfold;intros;assumption
     |apply (WFT_Forall ? ? ? H5);intros;elim (H4 X H7);
      apply (WFT_env_incl ? ? H10);simplify;unfold;intros;assumption]]
qed.

lemma JS_to_WFT1 : ∀G,T,U.G ⊢ T ⊴ U → G ⊢ T.
intros;elim (JS_to_WFT ? ? ? H);assumption;
qed.

lemma JS_to_WFT2 : ∀G,T,U.G ⊢ T ⊴ U → G ⊢ U.
intros;elim (JS_to_WFT ? ? ? H);assumption;
qed.

lemma WFE_Typ_subst : ∀H,x,B,T,U,G.
                      H @ mk_bound B x T :: G ⊢ ♦ → (G ⊢ U) →
                      H @ mk_bound B x U :: G ⊢ ♦.
intros 6;elim H 0
  [simplify;intros;inversion H1;intros
     [elim (nil_cons ? G (mk_bound B x T) H3)
     |destruct H7;autobatch]
  |intros;simplify;generalize in match H2;elim a;simplify in H4;
   inversion H4;intros
     [destruct H5
     |destruct H9;apply WFE_cons
        [apply (H1 H5 H3)
        |rewrite < (fv_env_extends ? x T U); assumption
        |apply (WFT_env_incl ? ? H8);
         rewrite < (fv_env_extends ? x T U);unfold;intros;
         assumption]]]
qed.

lemma WFE_bound_bound : ∀x,T,U,G.G ⊢ ♦ → !x ⊴  T ∈ G → !x ⊴ U ∈ G → T = U.
intros 5;elim H
  [lapply (not_in_list_nil ? ? H1);elim Hletin
  |elim (in_list_cons_case ? ? ? ? H6)
     [destruct H7;destruct;elim (in_list_cons_case ? ? ? ? H5)
        [destruct H7;reflexivity
        |elim H7;elim H3;apply boundinenv_natinfv;autobatch]
     |elim (in_list_cons_case ? ? ? ? H5)
        [destruct H8;elim H3;apply boundinenv_natinfv;autobatch
        |apply (H2 H8 H7)]]]
qed.

lemma WFT_to_incl: ∀G,T,U.(∀X.X ∉ fv_env G → X ∉ fv_type U →
    (mk_bound true X T::G ⊢ (subst_type_nat U (TFree X) O))) →
    fv_type U ⊆ fv_env G.
intros;elim (fresh_name (fv_type U@fv_env G));lapply(H a)
  [unfold;intros;lapply (fv_WFT ? x ? Hletin)
     [simplify in Hletin1;inversion Hletin1;intros
        [destruct H4;elim H1;autobatch
        |destruct H6;assumption]
     |apply in_FV_subst;assumption]
  |*:intro;apply H1;autobatch]
qed.

lemma incl_fv_env: ∀X,G,G1,U,P.
      fv_env (G1@ !X ⊴ U::G) ⊆ fv_env (G1@ !X ⊴ P::G).
intros.rewrite < fv_env_extends.apply incl_A_A.
qed.

lemma fv_append : ∀G,H.fv_env (G @ H) = fv_env G @ fv_env H.
intro;elim G;simplify;
[reflexivity
|elim a;simplify;elim b;simplify;lapply (H H1);rewrite > Hletin;reflexivity]
qed.
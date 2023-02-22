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

include "Fsub/part1a.ma".

inductive NTyp : Set \def
| TName : nat \to NTyp
| NTop : NTyp
| NArrow : NTyp \to NTyp \to NTyp
| NForall : nat \to NTyp \to NTyp \to NTyp.

record nbound : Set \def {
                           nistype : bool;
                           nname : nat;
                           nbtype : NTyp
                         }.

let rec encodetype T vars on T ≝
  match T with
  [ (TName n) ⇒ match (lookup n vars) with
    [ true ⇒ (TVar (posn vars n))
    | false ⇒ (TFree n)]
  | NTop ⇒ Top
  | (NArrow T1 T2) ⇒ Arrow (encodetype T1 vars) (encodetype T2 vars)
  | (NForall n2 T1 T2) ⇒ Forall (encodetype T1 vars) 
                                (encodetype T2 (n2::vars))].

let rec swap_NTyp u v T on T ≝
  match T with
     [(TName X) ⇒ (TName (swap u v X))
     |NTop ⇒ NTop
     |(NArrow T1 T2) ⇒ (NArrow (swap_NTyp u v T1) (swap_NTyp u v T2))
     |(NForall X T1 T2) ⇒ 
                  (NForall (swap u v X) (swap_NTyp u v T1) (swap_NTyp u v T2))].

let rec swap_Typ u v T on T \def
  match T with
     [(TVar n) ⇒ (TVar n)
     |(TFree X) ⇒ (TFree (swap u v X))
     |Top ⇒ Top
     |(Arrow T1 T2) ⇒ (Arrow (swap_Typ u v T1) (swap_Typ u v T2))
     |(Forall T1 T2) ⇒ (Forall (swap_Typ u v T1) (swap_Typ u v T2))].
                  
let rec var_NTyp (T:NTyp):list nat\def 
  match T with 
  [TName x ⇒ [x]
  |NTop ⇒ []
  |NArrow U V ⇒ (var_NTyp U)@(var_NTyp V)
  |NForall X U V ⇒ X::(var_NTyp U)@(var_NTyp V)].


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

definition filter_ntypes : list nbound → list nbound ≝
  λG.(filter ? G (λB.match B with [mk_nbound B X T ⇒ B])).

definition fv_Nenv : list nbound → list nat ≝
  λG.map nbound nat
    (λb.match b with 
      [mk_nbound (B:bool) (X:nat) (T:NTyp) ⇒ X]) (filter_ntypes G).
          
inductive NWFType : (list nbound) → NTyp → Prop ≝
  | NWFT_TName : ∀X,G.(X ∈ (fv_Nenv G))
                → (NWFType G (TName X))
  | NWFT_Top : ∀G.(NWFType G NTop)
  | NWFT_Arrow : ∀G,T,U.(NWFType G T) → (NWFType G U) →
                (NWFType G (NArrow T U))
  | NWFT_Forall : ∀G,X,T,U.(NWFType G T) →
                  (∀Y.Y ∉ (fv_Nenv G) → (Y ∈ (fv_NTyp U) → Y = X) → 
                    (NWFType ((mk_nbound true Y T) :: G) (swap_NTyp Y X U))) →
                 (NWFType G (NForall X T U)).

inductive NWFEnv : (list nbound) → Prop ≝
  | NWFE_Empty : (NWFEnv (nil ?))
  | NWFE_cons : ∀B,X,T,G.(NWFEnv G) →
                  X ∉ (fv_Nenv G) → 
                  (NWFType G T) → (NWFEnv ((mk_nbound B X T) :: G)).
          
inductive NJSubtype : (list nbound) → NTyp → NTyp → Prop ≝
  | NSA_Top : ∀G,T.(NWFEnv G) → (NWFType G T) → (NJSubtype G T NTop)
  | NSA_Refl_TVar : ∀G,X.(NWFEnv G)
                   → X ∈ (fv_Nenv G)
                   → (NJSubtype G (TName X) (TName X))
  | NSA_Trans_TVar : ∀G,X,T,U.
                     (mk_nbound true X U) ∈ G →
                     (NJSubtype G U T) → (NJSubtype G (TName X) T)
  | NSA_Arrow : ∀G,S1,S2,T1,T2.
               (NJSubtype G T1 S1) → (NJSubtype G S2 T2) →
               (NJSubtype G (NArrow S1 S2) (NArrow T1 T2))
  | NSA_All : ∀G,X,Y,S1,S2,T1,T2.
              (NJSubtype G T1 S1) →
              (∀Z.Z ∉ (fv_Nenv G) →
                  (Z ∈ (fv_NTyp S2) → Z = X) →
                  (Z ∈ (fv_NTyp T2) → Z = Y) →
              (NJSubtype ((mk_nbound true Z T1) :: G) 
                    (swap_NTyp Z X S2) (swap_NTyp Z Y T2))) →  
              (NJSubtype G (NForall X S1 S2) (NForall Y T1 T2)).
                                
let rec nt_len T ≝
  match T with
  [ TName X ⇒ O
  | NTop ⇒ O
  | NArrow T1 T2 ⇒ S (max (nt_len T1) (nt_len T2))
  | NForall X T1 T2 ⇒ S (max (nt_len T1) (nt_len T2)) ].     
                
definition encodeenv : list nbound → list bound ≝
  map nbound bound 
    (λb.match b with
       [ mk_nbound b x T ⇒ mk_bound b x (encodetype T []) ]). 
       
notation < "⌈ T ⌉ \sub l" with precedence 25 for @{'encode2 $T $l}.
interpretation "Fsub names to LN type encoding" 'encode2 T l = (encodetype T l).
notation < "⌈ G ⌉" with precedence 25 for @{'encode $G}.
interpretation "Fsub names to LN env encoding" 'encode G = (encodeenv G).
notation < "| T |" with precedence 25 for @{'abs $T}.
interpretation "Fsub named type length" 'abs T = (nt_len T).
interpretation "list length" 'abs l = (length ? l).
notation < "〈a,b〉 · T" with precedence 65 for @{'swap $a $b $T}.
interpretation "natural swap" 'swap a b n = (swap a b n).
interpretation "Fsub name swap in a named type" 'swap a b T = (swap_NTyp a b T).
interpretation "Fsub name swap in a LN type" 'swap a b T = (swap_Typ a b T).
interpretation "natural list swap" 'swap a b l = (swap_list a b l).

lemma eq_fv_Nenv_fv_env : ∀G. fv_Nenv G = fv_env (encodeenv G).
intro;elim G;simplify
  [reflexivity
  |elim a;elim b;simplify;rewrite < H;reflexivity]
qed.

lemma decidable_eq_Typ : ∀T,U:Typ.decidable (T = U).
intro;elim T
[cases U
 [cases (decidable_eq_nat n n1)
  [left;autobatch
  |right;intro;apply H;destruct H1;reflexivity]
 |*:right;intro;destruct]
|cases U
 [2:cases (decidable_eq_nat n n1)
  [left;autobatch
  |right;intro;apply H;destruct H1;reflexivity]
 |*:right;intro;destruct]
|cases U
 [3:left;reflexivity
 |*:right;intro;destruct]
|cases U
 [4:cases (H t2)
  [cases (H1 t3)
   [left;autobatch
   |right;intro;destruct H4;elim H3;reflexivity]
  |right;intro;destruct H3;elim H2;reflexivity]
 |*:right;intro;destruct]
|cases U
 [5:cases (H t2)
  [cases (H1 t3)
   [left;autobatch
   |right;intro;destruct H4;elim H3;reflexivity]
  |right;intro;destruct H3;elim H2;reflexivity]
 |*:right;intro;destruct]]
qed.

lemma decidable_eq_bound : ∀b,c:bound.decidable (b = c).
intros;cases b;cases c;cases (bool_to_decidable_eq b1 b2)
[cases (decidable_eq_nat n n1)
 [cases (decidable_eq_Typ t t1)
  [left;autobatch
  |right;intro;destruct H3;elim H2;reflexivity]
 |right;intro;destruct H2;elim H1;reflexivity]
|right;intro;destruct H1;elim H;reflexivity]
qed.

lemma in_Nenv_to_in_env: ∀l,n,n2.(mk_nbound true n n2) ∈ l → 
                 (mk_bound true n (encodetype n2 [])) ∈ (encodeenv l).
intros 3;elim l
  [elim (not_in_list_nil ? ? H)
  |inversion H1;intros;destruct;
     [simplify;apply in_list_head
     |elim a;simplify;apply in_list_cons;apply H;assumption]]
qed.
                 
lemma NTyp_len_ind : \forall P:NTyp \to Prop.
                       (\forall U.(\forall V.((nt_len V) < (nt_len U)) \to (P V))
                           \to (P U))
                       \to \forall T.(P T).
intros;
cut (∀m,n.max m n = m ∨ max m n = n) as Hmax
[|intros;unfold max;cases (leb m n);simplify
 [right;reflexivity
 |left;reflexivity]]
cut (∀S.nt_len S ≤ nt_len T → P S)
[|elim T
 [1,2:simplify in H1;apply H;intros;lapply (trans_le ??? H2 H1);
  elim (not_le_Sn_O ? Hletin)
 |simplify in H3;apply H;intros;lapply (trans_le ??? H4 H3);
  lapply (le_S_S_to_le ?? Hletin) as H5;clear Hletin;
  cases (Hmax (nt_len n) (nt_len n1));rewrite > H6 in H5
  [apply H1;assumption
  |apply H2;assumption]
 |simplify in H3;apply H;intros;lapply (trans_le ??? H4 H3);
  lapply (le_S_S_to_le ?? Hletin) as H5;clear Hletin;
  cases (Hmax (nt_len n1) (nt_len n2));rewrite > H6 in H5
  [apply H1;assumption
  |apply H2;assumption]]]
apply Hcut;apply le_n;
qed.

(*** even with this lemma, the following autobatch doesn't work properly 
lemma aaa : ∀x,y.S x ≤ y → x < y.
intros;apply H;
qed.
*)

lemma ntlen_arrow1 : ∀T1,T2.(nt_len T1) < (nt_len (NArrow T1 T2)).
intros;cases T2
[1,2:simplify;(*** autobatch *)apply le_S_S;autobatch
|*:whd in ⊢ (??%);apply le_S_S;apply le_m_max_m_n]
qed.

lemma ntlen_arrow2 : ∀T1,T2.(nt_len T2) < (nt_len (NArrow T1 T2)).
intros;cases T2
[1,2:simplify;autobatch
|*:whd in ⊢ (??%);apply le_S_S;apply le_n_max_m_n]
qed.
 
lemma ntlen_forall1 : ∀X,T1,T2.(nt_len T1) < (nt_len (NForall X T1 T2)). 
intros;cases T2
[1,2:simplify;(*** autobatch *)apply le_S_S;autobatch
|*:whd in ⊢ (??%);apply le_S_S;apply le_m_max_m_n]
qed.

lemma ntlen_forall2 : ∀X,T1,T2.(nt_len T2) < (nt_len (NForall X T1 T2)).
intros;cases T2
[1,2:simplify;autobatch
|*:whd in ⊢ (??%);apply le_S_S;apply le_n_max_m_n]
qed.

lemma eq_ntlen_swap : ∀X,Y,T.nt_len T = nt_len (swap_NTyp X Y T).
intros;elim T;simplify
[1,2:reflexivity
|*:autobatch paramodulation]
qed.

lemma fv_encode : ∀T,l1,l2.
                  (∀x.x ∈ (fv_NTyp T) →
                     (lookup x l1 = lookup x l2 ∧
                     (lookup x l1 = true → posn l1 x = posn l2 x))) →
                  (encodetype T l1 = encodetype T l2).
intro;elim T
  [simplify in H;elim (H n)
     [simplify;rewrite < H1;elim (lookup n l1) in H2;simplify
        [rewrite > H2;autobatch
        |reflexivity]
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
           |elim (H2 x);simplify
              [split
                 [rewrite < H5;reflexivity
                 |elim (eqb x n)
                    [simplify;reflexivity
                    |simplify in H7;rewrite < (H6 H7);reflexivity]]
              |apply in_list_to_in_list_append_r;
               apply (in_remove ? ? ? H4);assumption]]]
     |intros;apply H2;simplify;apply in_list_to_in_list_append_l;autobatch]]
qed.

theorem encode_swap : ∀a,x,T,vars.
                         (a ∈ (fv_NTyp T) → a ∈ vars) →
                         x ∈ vars →
                      encodetype T vars = 
                      encodetype (swap_NTyp a x T) (swap_list a x vars).
intros 3;elim T
  [elim (decidable_eq_nat n x)
     [rewrite > H2;simplify in match (swap_NTyp ? ? ?);rewrite > swap_right;
      simplify;lapply (lookup_swap a x x vars);rewrite > swap_right in Hletin;
      rewrite > Hletin;
      rewrite > (in_lookup ?? H1);simplify;lapply (posn_swap a x x vars);
      rewrite > swap_right in Hletin1;rewrite < Hletin1;reflexivity
     |elim (decidable_eq_nat n a);
        [rewrite < H3;simplify;rewrite < posn_swap;rewrite > lookup_swap;
         rewrite < H3 in H;simplify in H;rewrite > in_lookup;
           [simplify;reflexivity
           |apply H;apply in_list_head]
        |simplify in ⊢ (? ? ? (? % ?));rewrite > swap_other;
           [apply (fv_encode ? vars (swap_list a x vars));intros;
            simplify in H4;cut (x1 = n)
              [rewrite > Hcut;elim vars;simplify
                 [split [reflexivity|intro;reflexivity]
                 |elim H5;cut
                    (a1 = a ∨a1 = x ∨ (a1 ≠ a ∧ a1 ≠ x))
                    [|elim (decidable_eq_nat a1 a)
                       [left;left;assumption
                       |elim (decidable_eq_nat a1 x)
                          [left;right;assumption
                          |right;split;assumption]]]
                  decompose;
                  [rewrite > H10;rewrite > swap_left;
                   rewrite > (not_eq_to_eqb_false ? ? H2); 
                   rewrite > (not_eq_to_eqb_false ? ? H3);simplify;
                   split
                   [assumption
                   |intro;rewrite < (H7 H5);reflexivity]
                  |rewrite > H10;rewrite > swap_right; 
                   rewrite > (not_eq_to_eqb_false ? ? H2); 
                   rewrite > (not_eq_to_eqb_false ? ? H3);simplify;
                   split
                    [assumption
                    |intro;rewrite < (H7 H5);reflexivity]
                  |rewrite > (swap_other a x a1)
                    [rewrite < H6;split
                     [reflexivity
                     |elim (eqb n a1)
                      [simplify;reflexivity
                      |simplify in H5;rewrite < (H7 H5);reflexivity]]
                     |*:assumption]]]
              |inversion H4;intros;destruct;
                 [reflexivity
                 |elim (not_in_list_nil ? ? H5)]]
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
           |autobatch]
        |rewrite < (H1 (n::vars));
           [reflexivity
           |intro;apply in_list_cons;apply H2;apply in_list_to_in_list_append_r;
            apply (in_remove ? ? ? H4 H5)
           |autobatch]]
     |intro;apply H2;apply in_list_to_in_list_append_l;assumption
     |assumption]]
qed.

lemma encode_swap2 : ∀a:nat.∀x:nat.∀T:NTyp.
  a ∉ (fv_NTyp T) →
    ∀vars.x ∈ vars
       → encodetype T vars=encodetype (swap_NTyp a x T) (swap_list a x vars).
intros;apply (encode_swap ? ? ? ? ? H1);intro;elim (H H2);
qed.

lemma incl_fv_var : \forall T.(fv_NTyp T) ⊆ (var_NTyp T).
intro;elim T;simplify;unfold;intros
  [1,2:assumption
  |elim (in_list_append_to_or_in_list ? ? ? ? H2);autobatch
  |elim (decidable_eq_nat x n)
     [rewrite > H3;apply in_list_head
     |apply in_list_cons;elim (in_list_append_to_or_in_list ? ? ? ? H2)
        [autobatch
        |apply in_list_to_in_list_append_r;elim (remove_inlist ? ? ? H4);
         apply (H1 ? H5)]]]
qed.

lemma fv_encode2 : ∀T,l1,l2.
                      (∀x.x ∈ (fv_NTyp T) →
                           (lookup x l1 = lookup x l2 ∧
                            posn l1 x = posn l2 x)) →
                      (encodetype T l1 = encodetype T l2).
intros;apply fv_encode;intros;elim (H ? H1);split
  [assumption|intro;assumption]
qed.

lemma inlist_fv_swap : ∀x,y,b,T.
                   b ∉ (y::var_NTyp T) →
                   x ∈ (fv_NTyp (swap_NTyp b y T)) →
                   x ≠ y ∧ (x = b ∨ x ∈ (fv_NTyp T)).
intros 4;elim T
[simplify in H;simplify;simplify in H1;elim (decidable_eq_nat y n)
 [rewrite > H2 in H1;rewrite > swap_right in H1;inversion H1;intros;destruct;
  [split
   [unfold;intro;apply H;rewrite > H2;apply in_list_head
   |left;reflexivity]
  |elim (not_in_list_nil ? ? H3)]
 |elim (decidable_eq_nat b n)
  [rewrite > H3 in H;elim H;autobatch
  |rewrite > swap_other in H1
   [split
    [inversion H1;intros;destruct;
     [intro;apply H2;symmetry;assumption
     |elim (not_in_list_nil ? ? H4)]
    |autobatch]
   |*:intro;autobatch]]]
|simplify in H1;elim (not_in_list_nil ? ? H1)
|simplify;simplify in H3;simplify in H2;elim (in_list_append_to_or_in_list ? ? ? ? H3)
 [elim H
  [split
   [assumption
   |elim H6
    [left;assumption
    |right;apply in_list_to_in_list_append_l;assumption]]
  |intro;apply H2;inversion H5;intros;destruct;
   [apply in_list_head
   |apply in_list_cons;apply in_list_to_in_list_append_l;assumption]
  |assumption]
 |elim H1
  [split
   [assumption
   |elim H6
    [left;assumption
    |right;apply in_list_to_in_list_append_r;assumption]]
  |intro;apply H2;elim (in_list_append_to_or_in_list ?? [y] (var_NTyp n1) H5)
   [lapply (in_list_singleton_to_eq ??? H6);applyS in_list_head
   |autobatch]
  |assumption]]
|simplify;simplify in H3;simplify in H2;elim (in_list_append_to_or_in_list ? ? ? ? H3)
 [elim H
  [split
   [assumption
   |elim H6
    [left;assumption
    |right;autobatch]]
  |intro;apply H2;inversion H5;intros;destruct;
   [apply in_list_head
   |apply in_list_cons;elim (decidable_eq_nat b n);autobatch]
  |assumption]
 |elim H1
  [split
   [assumption
   |elim H6
    [left;assumption
    |right;apply in_list_to_in_list_append_r;apply inlist_remove
     [assumption
     |intro;elim (remove_inlist ? ? ? H4);apply H10;rewrite > swap_other
      [assumption
      |intro;rewrite > H8 in H7;rewrite > H11 in H7;apply H2;destruct;autobatch
      |destruct;assumption]]]]
  |intro;apply H2;inversion H5;intros;destruct;
   [apply in_list_head
   |apply in_list_cons;change in ⊢ (???%) with ((n::var_NTyp n1)@var_NTyp n2);
    elim (n::var_NTyp n1);simplify
    [assumption
    |elim (decidable_eq_nat b a);autobatch]]
  |elim(remove_inlist ? ? ? H4);assumption]]]
qed.

lemma inlist_fv_swap_r : ∀x,y,b,T.
                   (b ∉ (y::var_NTyp T)) →
                   ((x = b ∧ y ∈ (fv_NTyp T)) ∨
                    (x ≠ y ∧ x ∈ (fv_NTyp T))) →
                   x ∈ (fv_NTyp (swap_NTyp b y T)).
intros 4;elim T
[simplify;simplify in H;simplify in H1;cut (b ≠ n)
 [elim H1
  [elim H2;cut (y = n)
   [rewrite > Hcut1;rewrite > swap_right;rewrite > H3;apply in_list_head
   |inversion H4;intros;destruct;
    [autobatch
    |elim (not_in_list_nil ? ? H5)]]
  |elim H2;inversion H4;intros;destruct;
   [rewrite > (swap_other b y x)
    [apply in_list_head
    |intro;autobatch
    |assumption]
   |elim (not_in_list_nil ? ? H5)]]
 |intro;apply H;autobatch]
|simplify in H1;decompose;elim (not_in_list_nil ? ? H3)
|simplify;simplify in H3;cut (\lnot (in_list ? b (y::var_NTyp n1)))
 [cut (¬(in_list ? b (y::var_NTyp n)))
  [decompose
   [elim (in_list_append_to_or_in_list ? ? ? ? H5)
    [apply in_list_to_in_list_append_l;apply H
     [assumption
     |left;split;assumption]
    |apply in_list_to_in_list_append_r;apply H1
     [assumption
     |left;split;assumption]]
   |elim (in_list_append_to_or_in_list ? ? ? ? H5)
    [apply in_list_to_in_list_append_l;apply H;
     [assumption
     |right;split;assumption]
    |apply in_list_to_in_list_append_r;apply H1
     [assumption
     |right;split;assumption]]]
  |intro;apply H2;inversion H4;intros;destruct;simplify;autobatch]
 |intro;apply H2;inversion H4;intros;destruct;simplify;autobatch]
|simplify;simplify in H3;cut (¬(in_list ? b (y::var_NTyp n1)))
 [cut (¬(in_list ? b (y::var_NTyp n2)))
  [decompose
   [elim (in_list_append_to_or_in_list ? ? ? ? H5)
    [apply in_list_to_in_list_append_l;apply H
     [assumption
     |left;split;assumption]
    |apply in_list_to_in_list_append_r;apply inlist_remove
     [apply H1
      [assumption
      |left;split
       [assumption|elim (remove_inlist ? ? ? H4);assumption]]
     |elim (remove_inlist ? ? ? H4);elim (decidable_eq_nat b n)
      [rewrite > H8;rewrite > swap_left;intro;apply H7;autobatch paramodulation
      |rewrite > swap_other
       [rewrite > H3;assumption
       |intro;apply H8;symmetry;assumption
       |intro;apply H7;symmetry;assumption]]]]
   |elim (in_list_append_to_or_in_list ? ? ? ? H5)
    [apply in_list_to_in_list_append_l;apply H
     [assumption
     |right;split;assumption]
    |apply in_list_to_in_list_append_r;apply inlist_remove
     [apply H1;
      [assumption
      |right;split
       [assumption|elim (remove_inlist ? ? ? H4);assumption]]
     |elim (decidable_eq_nat b n)
      [rewrite > H6;rewrite > swap_left;assumption
      |elim (decidable_eq_nat y n)
       [rewrite > H7;rewrite > swap_right;intro;apply Hcut1;
        apply in_list_cons;apply incl_fv_var;elim (remove_inlist ? ? ? H4);
        rewrite < H8;assumption
       |rewrite > (swap_other b y n)
        [elim (remove_inlist ? ? ? H4);assumption
        |intro;apply H6;symmetry;assumption
        |intro;apply H7;symmetry;assumption]]]]]]
  |intro;apply H2;inversion H4;simplify;intros;destruct;
   [apply in_list_head
   |change in ⊢ (???%) with ((y::n::var_NTyp n1)@var_NTyp n2);autobatch]]
 |intro;apply H2;inversion H4;simplify;intros;destruct;autobatch depth=4]]
qed.               
                      
lemma encode_append : ∀T,U,n,l.length ? l ≤ n →
        subst_type_nat (encodetype T l) U n = encodetype T l.
intros 2;elim T;simplify
  [elim (bool_to_decidable_eq (lookup n l) true)
     [rewrite > H1;simplify;lapply (lookup_in ? ? H1);
      lapply (posn_length ? ? Hletin);cut (posn l n ≠ n1)
        [rewrite > (not_eq_to_eqb_false ? ? Hcut);simplify;reflexivity
        |intro;rewrite > H2 in Hletin1;unfold in Hletin1;autobatch]
     |cut (lookup n l = false)
        [rewrite > Hcut;reflexivity
        |elim (lookup n l) in H1;
           [elim H1;reflexivity|reflexivity]]]
  |reflexivity
  |autobatch
  |rewrite > (H ? ? H2);rewrite > H1;
     [reflexivity
     |simplify;autobatch]]
qed.

lemma encode_subst_simple : ∀X,T,l.
  encodetype T l = subst_type_nat (encodetype T (l@[X])) (TFree X) (length ? l).
intros 2;elim T;simplify
[cut (lookup n l = true → posn l n = posn (l@[X]) n)
 [elim (bool_to_decidable_eq (lookup n l) true) in Hcut
  [cut (lookup n (l@[X]) = true)
   [rewrite > H;rewrite > Hcut;simplify;
    cut (eqb (posn (l@[X]) n) (length nat l) = false)
    [rewrite > Hcut1;simplify;rewrite < (H1 H);reflexivity
    |elim l in H 0
     [simplify;intro;destruct
     |intros 2;simplify;elim (eqb n a);simplify
      [reflexivity
      |simplify in H3;apply (H H2)]]]
   |elim l in H
    [simplify in H;destruct
    |generalize in match H2;simplify;elim (eqb n a) 0;simplify;intro
     [reflexivity
     |apply (H H3)]]]
  |cut (lookup n l = false)
   [elim (decidable_eq_nat n X)
    [rewrite > Hcut;rewrite > H2;cut (lookup X (l@[X]) = true)
     [rewrite > Hcut1;simplify;cut (eqb (posn (l@[X]) X) (length nat l) = true)
      [rewrite > Hcut2;simplify;reflexivity
      |elim l in Hcut 0
       [intros;simplify;rewrite > eqb_n_n;simplify;reflexivity
       |simplify;intros 2;rewrite > H2;elim (eqb X a);simplify in H4
        [destruct
        |apply (H3 H4)]]]
     |elim l;simplify
      [rewrite > eqb_n_n;reflexivity
      |elim (eqb X a);simplify
       [reflexivity
       |assumption]]]
    |cut (lookup n l = lookup n (l@[X]))
     [rewrite < Hcut1;rewrite > Hcut;simplify;reflexivity
     |elim l;simplify
      [rewrite > (not_eq_to_eqb_false ? ? H2);simplify;reflexivity
      |elim (eqb n a);simplify
       [reflexivity
       |assumption]]]]
   |elim (lookup n l) in H
    [elim H;reflexivity|reflexivity]]]
 |elim l 0
  [intro;simplify in H;destruct
  |simplify;intros 2;elim (eqb n a);simplify
   [reflexivity
   |simplify in H1;rewrite < (H H1);reflexivity]]]
|reflexivity
|rewrite < H;rewrite < H1;reflexivity
|rewrite < H;rewrite < (associative_append ? [n] l [X]);
 rewrite < (H1 ([n]@l));reflexivity]
qed.

lemma encode_subst : ∀T,X,Y,l.X ∉ l → Y ∉ l →
                              (X ∈ (fv_NTyp T) → X = Y) → 
                              encodetype (swap_NTyp X Y T) l =
                 subst_type_nat (encodetype T (l@[Y])) (TFree X) (length ? l).
apply NTyp_len_ind;intro;elim U
[elim (decidable_eq_nat n X)
 [rewrite > H4 in H3;rewrite > H4;rewrite > H3
  [simplify in ⊢ (?? (?%?) ?);rewrite > swap_same;
   cut (lookup Y (l@[Y]) = true)
   [simplify;rewrite > Hcut;rewrite > (not_nat_in_to_lookup_false ? ? H2);
    simplify;cut (posn (l@[Y]) Y = length ? l)
    [rewrite > Hcut1;rewrite > eqb_n_n;reflexivity
    |elim l in H2;simplify
     [rewrite > eqb_n_n;reflexivity
     |elim (decidable_eq_nat Y a)
      [elim H5;rewrite > H6;apply in_list_head
      |rewrite > (not_eq_to_eqb_false ? ? H6);simplify;rewrite < H2
       [reflexivity
       |intro;autobatch]]]]
   |elim l;simplify
    [rewrite > eqb_n_n;reflexivity
    |rewrite > H5;elim (eqb Y a);reflexivity]]
  |simplify;apply in_list_head]
 |elim (decidable_eq_nat Y n);
  [rewrite < H5;simplify;rewrite > swap_right;
   rewrite > (not_nat_in_to_lookup_false ? ? H1);
   cut (lookup Y (l@[Y]) = true)
   [rewrite > Hcut;simplify;cut (posn (l@[Y]) Y = length ? l)
    [rewrite > Hcut1;rewrite > eqb_n_n;reflexivity
    |elim l in H2;simplify
     [rewrite > eqb_n_n;reflexivity
     |elim (decidable_eq_nat Y a)
      [elim H6;applyS in_list_head
      |rewrite > (not_eq_to_eqb_false ? ? H7);simplify;rewrite < H2
       [reflexivity
       |intro;autobatch]]]]
   |elim l;simplify
    [rewrite > eqb_n_n;reflexivity
    |elim (eqb Y a);simplify;autobatch]]
  |simplify;rewrite > (swap_other X Y n)
   [cut (lookup n l = lookup n (l@[Y]) ∧ 
         (lookup n l = true → posn l n = posn (l@[Y]) n))
    [elim Hcut;rewrite > H6;elim (lookup n (l@[Y])) in H7 H6;simplify;
     [rewrite < H7;elim l in H6
      [simplify in H6;destruct
      |elim (decidable_eq_nat n a);simplify
       [rewrite > (eq_to_eqb_true ? ? H9);reflexivity
       |rewrite > (not_eq_to_eqb_false ? ? H9);
        simplify;elim (eqb (posn l1 n) (length nat l1)) in H6
        [simplify in H8;simplify in H6;
         rewrite > (not_eq_to_eqb_false ? ? H9) in H8;
         simplify in H8;lapply (H6 H8);destruct
        |reflexivity]]
      |*:assumption]
     |reflexivity]
    |elim l;split
     [simplify;cut (n ≠ Y)
      [rewrite > (not_eq_to_eqb_false ? ? Hcut);reflexivity
      |intro;apply H5;symmetry;assumption]
     |intro;simplify in H6;destruct H6
     |elim H6;simplify;rewrite < H7;reflexivity
     |simplify;elim (eqb n a);simplify
      [reflexivity
      |simplify in H7;elim H6;rewrite < (H9 H7);reflexivity]]]
   |assumption
   |intro;apply H5;symmetry;assumption]]]
|reflexivity
|simplify;rewrite < (H2 n ? ? ? ? H3 H4) 
 [rewrite < (H2 n1 ? ? ? ? H3 H4);
  [1,2:autobatch
  |intro;apply H5;simplify;autobatch]
 |autobatch
 |intro;apply H5;simplify;autobatch]
|simplify;rewrite < (H2 n1 ? ? ? ? H3 H4) 
 [cut (l = swap_list X Y l)
  [|elim l in H3 H4;simplify
   [reflexivity
   |elim (decidable_eq_nat a X)
    [elim H4;applyS in_list_head
    |elim (decidable_eq_nat a Y)
     [elim H6;applyS in_list_head
     |rewrite > (swap_other X Y a)
      [rewrite < H3
       [reflexivity
       |*:intro;autobatch]
      |*:assumption]]]]]
  elim (decidable_eq_nat n Y)
  [rewrite > H6;
   rewrite > (fv_encode (swap_NTyp X Y n2) (swap X Y Y::l) (swap_list X Y (Y::l)));
   [rewrite < (encode_swap X Y n2);
    [rewrite < (fv_encode ? (Y::l) (Y::l@[Y]))
     [rewrite > encode_append;
      [reflexivity
      |simplify;constructor 1]
     |intros;simplify;elim (decidable_eq_nat x Y)
      [rewrite > (eq_to_eqb_true ? ? H8);simplify;split
       [reflexivity|intro;reflexivity]
      |rewrite > (not_eq_to_eqb_false ? ? H8);simplify;elim l;simplify
       [rewrite > (not_eq_to_eqb_false ? ? H8);simplify;split 
        [reflexivity|intro;destruct H9]
       |elim (eqb x a);simplify
        [split [reflexivity|intro;reflexivity]
        |elim H9;split
         [assumption
         |intro;rewrite < (H11 H12);reflexivity]]]]]
    |intro;elim (decidable_eq_nat X Y)
     [rewrite > H8;apply in_list_head
     |elim H8;apply H5;simplify;apply in_list_to_in_list_append_r;
      rewrite > H6;apply (in_remove ? ? ? H8 H7)]
    |apply in_list_head]
   |intros;simplify;rewrite > swap_right;rewrite < Hcut;
    split [reflexivity|intro;reflexivity]]
  |elim (decidable_eq_nat n X)
   [rewrite > H7;
    rewrite > (fv_encode (swap_NTyp X Y n2) (swap X Y X::l) (swap_list X Y (X::l)))
    [rewrite > (encode_swap X Y n2);
     [simplify;
      cut (swap X Y X::swap_list X Y (l@[Y]) = 
           (swap X Y X::swap_list X Y l)@[X])
      [rewrite > Hcut1;cut (S (length ? l) = (length ? (swap X Y X::swap_list X Y l)))
       [rewrite > Hcut2;
        rewrite < (encode_subst_simple X (swap_NTyp X Y n2) (swap X Y X::swap_list X Y l));
        reflexivity
       |simplify;elim l
        [reflexivity
        |simplify;rewrite < H8;reflexivity]]
      |simplify;elim l;simplify
       [rewrite > swap_right;reflexivity
       |destruct;rewrite > Hcut1;reflexivity]]
     |intro;apply in_list_head
     |apply in_list_cons;elim l;simplify;autobatch]
    |intros;simplify;rewrite < Hcut;
     split [reflexivity|intro;reflexivity]]
   |rewrite > (swap_other X Y n)
    [rewrite < (associative_append ? [n] l [Y]);
     cut (S (length nat l) = length nat (n::l)) [|reflexivity]
     rewrite > Hcut1;rewrite < (H2 n2);
     [reflexivity
     |autobatch
     |intro;apply H7;inversion H8;intros;destruct;
      [reflexivity
      |elim (H3 H9)]
     |intro;apply H6;inversion H8;intros;destruct;
      [reflexivity
      |elim (H4 H9)]
     |intro;apply H5;simplify;apply in_list_to_in_list_append_r;
      apply (in_remove ? ? ? ? H8);intro;apply H7;symmetry;assumption]
    |*:assumption]]]
 |autobatch
 |intro;apply H5;simplify;autobatch]]
qed.

lemma in_fvNTyp_in_fvNenv : ∀G,T.(NWFType G T) → (fv_NTyp T) ⊆ (fv_Nenv G).
intros;elim H;simplify;unfold;intros;
[inversion H2;intros;destruct;
 [assumption
 |elim (not_in_list_nil ? ? H3)]
|elim (not_in_list_nil ? ? H1)
|elim (in_list_append_to_or_in_list ? ? ? ? H5)
 [apply (H2 ? H6)|apply (H4 ? H6)]
|elim (in_list_append_to_or_in_list ? ? ? ? H5)
 [apply H2;assumption
 |elim (fresh_name (x::fv_Nenv l@var_NTyp n2));lapply (H4 a)
  [cut (a ≠ x ∧ x ≠ n)
   [elim Hcut;lapply (Hletin x)
    [simplify in Hletin1;inversion Hletin1;intros;destruct;
     [elim H8;reflexivity
     |assumption]
    |generalize in match H6;generalize in match H7;elim n2
     [simplify in H11;elim (decidable_eq_nat n n3)
      [rewrite > (eq_to_eqb_true ? ? H12) in H11;simplify in H11;
       elim (not_in_list_nil ? ? H11)
      |rewrite > (not_eq_to_eqb_false ? ? H12) in H11;
       simplify in H11;inversion H11;intros
       [destruct;simplify;rewrite > swap_other
        [apply in_list_head
        |intro;apply H8;rewrite > H13;reflexivity
        |intro;apply H9;rewrite > H13;reflexivity]
       |destruct;elim (not_in_list_nil ? ? H13)]]
     |simplify in H11;elim (not_in_list_nil ? ? H11)
     |simplify in H13;simplify;elim (remove_inlist ? ? ? H13);
      elim (in_list_append_to_or_in_list ? ? ? ? H14)
      [apply in_list_to_in_list_append_l;apply H10
       [intro;apply H12;simplify;
        rewrite < (associative_append ? [x] (fv_Nenv l) (var_NTyp n3 @ var_NTyp n4));
        elim (in_list_append_to_or_in_list ? ? (x::fv_Nenv l) (var_NTyp n3) H17);
        autobatch depth=4
       |apply (in_remove ? ? ? H15 H16)]
      |apply in_list_to_in_list_append_r;apply H11
       [intro;apply H12;simplify;
        rewrite < (associative_append ? [x] (fv_Nenv l) (var_NTyp n3 @ var_NTyp n4));
        elim (in_list_append_to_or_in_list ? ? (x::fv_Nenv l) (var_NTyp n4) H17);
        autobatch depth=5
       |apply (in_remove ? ? ? H15 H16)]]
     |simplify;simplify in H13;elim (remove_inlist ? ? ? H13);
      elim (in_list_append_to_or_in_list ???? H14)
      [apply in_list_to_in_list_append_l;apply H10;
       [rewrite < (associative_append ? [x] (fv_Nenv l) (var_NTyp n4));
        intro;apply H12;simplify;
        rewrite < (associative_append ? [x] (fv_Nenv l) (n3::var_NTyp n4@var_NTyp n5));
        elim (in_list_append_to_or_in_list ???? H17);autobatch depth=4
       |autobatch]
      |apply in_list_to_in_list_append_r;apply in_remove;
       [elim (remove_inlist ? ? ? H16);intro;apply H18;
        elim (swap_case a n n3)
        [elim H20
         [elim H8;symmetry;rewrite < H21;assumption
         |elim H9;rewrite < H21;assumption]
        |rewrite < H20;assumption]
       |apply H11; 
        [rewrite < (associative_append ? [x] (fv_Nenv l) (var_NTyp n5));
         intro;apply H12;simplify;
         rewrite < (associative_append ? [x] (fv_Nenv l) (n3::var_NTyp n4 @ var_NTyp n5));
         elim (in_list_append_to_or_in_list ???? H17);autobatch depth=4
        |elim (remove_inlist ? ? ? H16);autobatch]]]]]
   |split
    [intro;apply H7;rewrite > H8;apply in_list_head
    |elim (remove_inlist ? ? ? H6);assumption]]
  |intro;autobatch depth=4
  |intro;elim H7;autobatch]]]
qed.

lemma fv_NTyp_fv_Typ : ∀T,X,l.X ∈ (fv_NTyp T) → X ∉ l → 
                          X ∈ (fv_type (encodetype T l)).
intros 2;elim T;simplify
  [simplify in H;cut (X = n)
     [rewrite < Hcut;generalize in match (lookup_in X l);elim (lookup X l)
        [elim H1;apply H2;reflexivity
        |simplify;apply in_list_head]
     |inversion H;intros;destruct;
        [reflexivity
        |elim (not_in_list_nil ? ? H2)]]
  |simplify in H;elim (not_in_list_nil ? ? H)
  |simplify in H2;elim (in_list_append_to_or_in_list ? ? ? ? H2);autobatch
  |simplify in H2;
   elim (in_list_append_to_or_in_list ? ? ? ? H2)
     [autobatch
     |apply in_list_to_in_list_append_r;
      elim (remove_inlist ? ? ? H4);apply (H1 ? H5);intro;apply H6;
      inversion H7;intros;destruct;
        [reflexivity
        |elim (H3 H8)]]]
qed.

lemma adeq_WFT : ∀G,T.NWFType G T → WFType (encodeenv G) (encodetype T []).
intros;elim H;simplify
[apply WFT_TFree;rewrite < eq_fv_Nenv_fv_env;assumption
|2,3:autobatch
|apply WFT_Forall
 [assumption
 |intros;rewrite < (encode_subst n2 X n []);
  [simplify in H4;apply H4
   [rewrite > (eq_fv_Nenv_fv_env l);assumption
   |elim (decidable_eq_nat X n)
    [assumption
    |elim H6;apply (fv_NTyp_fv_Typ ??? H8);autobatch]]
  |4:intro;elim (decidable_eq_nat X n)
   [assumption
   |elim H6;cut (¬(in_list ? X [n]))
    [generalize in match Hcut;generalize in match [n];
     generalize in match H7;elim n2
     [simplify in H9;generalize in match H9;intro;inversion H9;intros;destruct;
      [simplify;generalize in match (lookup_in X l1);elim (lookup X l1)
       [elim H10;apply H12;reflexivity
       |simplify;apply in_list_head]
      |elim (not_in_list_nil ? ? H12)]
     |simplify in H9;elim (not_in_list_nil ? ? H9)
     |simplify;simplify in H11;
      elim (in_list_append_to_or_in_list ? ? ? ? H11);autobatch
     |simplify;simplify in H11;elim (in_list_append_to_or_in_list ? ? ? ? H11);
      [autobatch
      |elim (remove_inlist ? ? ? H13);apply in_list_to_in_list_append_r;
       apply (H10 H14);intro;inversion H16;intros;destruct;
       [elim H15;reflexivity
       |elim H12;assumption]]]
    |intro;elim H8;inversion H9;intros;destruct;
     [autobatch
     |elim (not_in_list_nil ? ? H10)]]]
  |*:apply not_in_list_nil]]] 
qed.

lemma not_in_list_encodetype : \forall T,l,x.x ∈ l \to
                      \lnot x ∈ (fv_type (encodetype T l)).
intro;elim T;simplify
  [apply (bool_elim ? (lookup n l));intro;simplify
     [apply not_in_list_nil
     |intro;inversion H2;intros;destruct;
        [rewrite > (in_lookup ? ? H) in H1;destruct H1
        |apply (not_in_list_nil ? ? H3)]]
  |apply not_in_list_nil
  |intro;elim (in_list_append_to_or_in_list ???? H3);autobatch
  |intro;elim (in_list_append_to_or_in_list ???? H3);
     [autobatch
     |apply (H1 (n::l) x ? H4);apply in_list_cons;assumption]]
qed.

lemma incl_fv_encode_fv : \forall T,l.(fv_type (encodetype T l)) ⊆ (fv_NTyp T).
intro;elim T;simplify;unfold;
  [intro;elim (lookup n l);simplify in H
     [elim (not_in_list_nil ? ? H)
     |assumption]
  |intros;elim (not_in_list_nil ? ? H)
  |intros;elim (in_list_append_to_or_in_list ? ? ? ? H2);autobatch
  |intros;elim (in_list_append_to_or_in_list ? ? ? ? H2)
     [autobatch
     |apply in_list_to_in_list_append_r;apply in_remove
        [intro;apply (not_in_list_encodetype n2 (n::l) x);autobatch;
        |autobatch]]]
qed.

lemma decidable_inlist_nat : ∀l:list nat.∀n.decidable (n ∈ l).
intros;elim l
[right;autobatch
|elim H
 [left;autobatch
 |elim (decidable_eq_nat n a)
  [left;autobatch
  |right;intro;apply H2;inversion H3;intros;destruct;
   [reflexivity
   |elim (H1 H4)]]]]
qed.

lemma adeq_WFT2 : ∀G1,T1.WFType G1 T1 → 
                     ∀G2,T2.G1 = encodeenv G2 → T1 = encodetype T2 [] → 
                   NWFType G2 T2.
intros 3;elim H
  [rewrite > H2 in H1;rewrite < eq_fv_Nenv_fv_env in H1;
   cut (T2 = TName n) 
     [|elim T2 in H3
        [simplify in H3;destruct;reflexivity
        |simplify in H3;destruct H3
        |simplify in H5;destruct H5
        |simplify in H5;destruct H5]]
   rewrite > Hcut;apply NWFT_TName;assumption
  |cut (T2 = NTop) 
     [|elim T2 in H2
        [simplify in H2;destruct H2
        |reflexivity
        |simplify in H4;destruct H4
        |simplify in H4;destruct H4]]
   rewrite > Hcut;apply NWFT_Top;
  |cut (∃U,V.T2 = (NArrow U V)) 
     [|elim T2 in H6
        [1,2:simplify in H6;destruct H6
        |autobatch;
        |simplify in H8;destruct H8]]
   elim Hcut;elim H7;rewrite > H8 in H6;simplify in H6;destruct;autobatch size=7
  |cut (\exists Z,U,V.T2 = NForall Z U V) 
     [|elim T2 in H6
        [1,2:simplify in H6;destruct
        |simplify in H8;destruct
        |autobatch depth=4]]]
   elim Hcut;elim H7;elim H8;clear Hcut H7 H8;rewrite > H9;
   rewrite > H9 in H6;simplify in H6;destruct;apply NWFT_Forall
     [autobatch
     |intros;elim (decidable_inlist_nat (fv_NTyp a2) Y)
      [lapply (H6 H7) as H8;rewrite > H8;rewrite > (? : swap_NTyp a a a2 = a2)
       [apply (H4 Y)
        [4:rewrite > H8;change in ⊢ (?? (? (??%) ??) ?) with ([]@[a]);
         symmetry;change in ⊢ (??? (???%)) with (length nat []);autobatch
        |*:autobatch]
       |elim a2;simplify;autobatch]
      |apply (H4 Y)
       [1,3:autobatch
       |intro;autobatch
       |symmetry;apply (encode_subst a2 Y a [])
        [3:intro;elim (H7 H8)
        |*:autobatch]]]]
qed.

lemma adeq_WFE : ∀G.NWFEnv G → WFEnv (encodeenv G).
intros;elim H;simplify;autobatch;
qed.

lemma NWFT_env_incl : ∀G,T.NWFType G T → ∀H.(fv_Nenv G) ⊆ (fv_Nenv H) 
                      → NWFType H T.
intros 3;elim H
  [4:apply NWFT_Forall
     [autobatch
     |intros;apply (H4 ? ? H8);
        [intro;apply H7;apply (H6 ? H9)
        |unfold;intros;simplify;simplify in H9;inversion H9;intros;
         destruct;simplify;
         [autobatch
         |apply in_list_cons;apply H6;apply H10]]]
  |*:autobatch]
qed.

lemma NJS_fv_to_fvNenv : ∀G,T,U.NJSubtype G T U → 
  fv_NTyp T ⊆ fv_Nenv G ∧ fv_NTyp U ⊆ fv_Nenv G.
intros;elim H;simplify;
[split
 [autobatch
 |unfold;intros;elim (not_in_list_nil ?? H3)]
|split;unfold;intros;rewrite > (in_list_singleton_to_eq ??? H3);assumption
|decompose;split;try autobatch;unfold;intros;
 rewrite > (in_list_singleton_to_eq ??? H3);
 generalize in match (refl_eq ? (mk_nbound true n n2));
 elim H1 in ⊢ (???% → %)
 [rewrite < H6;simplify;apply in_list_head
 |cases a1;cases b;simplify;
  [apply in_list_cons;apply H7;assumption
  |apply H7;assumption]]
|decompose;split;unfold;intros;
 [elim (in_list_append_to_or_in_list ???? H4);autobatch
 |elim (in_list_append_to_or_in_list ???? H4);autobatch]
|decompose;split;unfold;intros;
 [elim (in_list_append_to_or_in_list ? ? ? ? H2)
  [autobatch
  |elim (fresh_name (x::fv_Nenv l@var_NTyp n3@var_NTyp n5));lapply (H4 a)
   [cut (a ≠ x ∧ x ≠ n)
    [elim Hcut;elim Hletin;lapply (H11 x)
     [simplify in Hletin1;inversion Hletin1;intros;destruct;
      [elim Hcut;elim H13;reflexivity
      |assumption]
     |elim n3 in H7 H8
      [simplify in H7;elim (decidable_eq_nat n n6)
       [rewrite > (eq_to_eqb_true ? ? H13) in H7;simplify in H7;
        elim (not_in_list_nil ? ? H7)
       |rewrite > (not_eq_to_eqb_false ? ? H13) in H7;
        simplify in H7;inversion H7;intros
        [destruct;simplify;rewrite > swap_other
         [apply in_list_head
         |intro;apply H8;rewrite > H14;autobatch
         |intro;apply H13;rewrite > H14;reflexivity]
        |destruct;elim (not_in_list_nil ? ? H14)]]
      |simplify in H7;elim (not_in_list_nil ? ? H7)
      |simplify in H14;simplify;elim (remove_inlist ? ? ? H13);
       simplify in H15;elim (in_list_append_to_or_in_list ? ? ? ? H15)
       [apply in_list_to_in_list_append_l;apply H7
        [apply (in_remove ? ? ? H16 H17)
        |intro;apply H14;simplify;
         rewrite < (associative_append ? [x] (fv_Nenv l) ((var_NTyp n6 @ var_NTyp n7)@var_NTyp n5));
         elim (in_list_append_to_or_in_list ? ? (x::fv_Nenv l) (var_NTyp n6@var_NTyp n5) H18);
         [apply in_list_to_in_list_append_l;apply H19
         |apply in_list_to_in_list_append_r;
          elim (in_list_append_to_or_in_list ???? H19);autobatch]]
       |apply in_list_to_in_list_append_r;apply H8
        [apply (in_remove ? ? ? H16 H17)
        |intro;apply H14;simplify;
         rewrite < (associative_append ? [x] (fv_Nenv l) ((var_NTyp n6 @ var_NTyp n7)@var_NTyp n5));
         elim (in_list_append_to_or_in_list ? ? (x::fv_Nenv l) (var_NTyp n7@var_NTyp n5) H18);
         [apply in_list_to_in_list_append_l;apply H19
         |apply in_list_to_in_list_append_r;
          elim (in_list_append_to_or_in_list ???? H19);autobatch]]]
      |simplify in H14;simplify;elim (remove_inlist ? ? ? H13);
       simplify in H15;elim (in_list_append_to_or_in_list ? ? ? ? H15)
       [apply in_list_to_in_list_append_l;apply H7
        [apply (in_remove ? ? ? H16 H17)
        |intro;apply H14;simplify;
         rewrite < (associative_append ? [x] (fv_Nenv l) (n6::(var_NTyp n7 @ var_NTyp n8)@var_NTyp n5));
         elim (in_list_append_to_or_in_list ? ? (x::fv_Nenv l) (var_NTyp n7@var_NTyp n5) H18);
         [apply in_list_to_in_list_append_l;apply H19
         |apply in_list_to_in_list_append_r;apply in_list_cons;
          elim (in_list_append_to_or_in_list ???? H19);autobatch]]
       |apply in_list_to_in_list_append_r;apply in_remove;
        [elim (remove_inlist ??? H13);intro;apply H19;
         elim (swap_case a n n6)
         [elim H21
          [elim H14;rewrite < H22;rewrite < H20;apply in_list_head
          |autobatch paramodulation]
         |elim (remove_inlist ??? H17);elim H23;autobatch paramodulation]
        |apply H8
         [apply (in_remove ? ? ? H16);elim (remove_inlist ??? H17);assumption
         |intro;apply H14;simplify;
          rewrite < (associative_append ? [x] (fv_Nenv l) (n6::(var_NTyp n7 @ var_NTyp n8)@var_NTyp n5));
          elim (in_list_append_to_or_in_list ? ? (x::fv_Nenv l) (var_NTyp n8@var_NTyp n5) H18);
          [apply in_list_to_in_list_append_l;apply H19
          |apply in_list_to_in_list_append_r;apply in_list_cons;
           elim (in_list_append_to_or_in_list ???? H19);autobatch]]]]]]
    |split
     [intro;apply H8;rewrite > H9;apply in_list_head
     |elim (remove_inlist ? ? ? H7);assumption]]
   |intro;autobatch depth=4
   |3,4:intro;elim H8;apply in_list_cons;autobatch depth=4]]
 |elim (in_list_append_to_or_in_list ? ? ? ? H2)
  [autobatch
  |elim (fresh_name (x::fv_Nenv l@var_NTyp n3@var_NTyp n5));lapply (H4 a)
   [cut (a ≠ x ∧ x ≠ n1)
    [elim Hcut;elim Hletin;lapply (H12 x)
     [simplify in Hletin1;inversion Hletin1;intros;destruct;
      [elim Hcut;elim H13;reflexivity
      |assumption]
     |elim n5 in H7 H8
      [simplify in H7;elim (decidable_eq_nat n1 n6)
       [rewrite > (eq_to_eqb_true ? ? H13) in H7;simplify in H7;
        elim (not_in_list_nil ? ? H7)
       |rewrite > (not_eq_to_eqb_false ? ? H13) in H7;
        simplify in H7;inversion H7;intros
        [destruct;simplify;rewrite > swap_other
         [apply in_list_head
         |intro;apply H8;rewrite > H14;autobatch
         |intro;apply H13;rewrite > H14;reflexivity]
        |destruct;elim (not_in_list_nil ? ? H14)]]
      |simplify in H7;elim (not_in_list_nil ? ? H7)
      |simplify in H14;simplify;elim (remove_inlist ? ? ? H13);
       simplify in H15;elim (in_list_append_to_or_in_list ? ? ? ? H15)
       [apply in_list_to_in_list_append_l;apply H7
        [apply (in_remove ? ? ? H16 H17)
        |intro;apply H14;simplify;
         rewrite < (associative_append ? [x] (fv_Nenv l) (var_NTyp n3 @ var_NTyp n6@var_NTyp n7));
         elim (in_list_append_to_or_in_list ? ? (x::fv_Nenv l) (var_NTyp n3@var_NTyp n6) H18);
         [apply in_list_to_in_list_append_l;apply H19
         |apply in_list_to_in_list_append_r;
          elim (in_list_append_to_or_in_list ???? H19);autobatch]]
       |apply in_list_to_in_list_append_r;apply H8
        [apply (in_remove ? ? ? H16 H17)
        |intro;apply H14;simplify;
         rewrite < (associative_append ? [x] (fv_Nenv l) (var_NTyp n3 @ var_NTyp n6@var_NTyp n7));
         elim (in_list_append_to_or_in_list ? ? (x::fv_Nenv l) (var_NTyp n3@var_NTyp n7) H18);
         [apply in_list_to_in_list_append_l;apply H19
         |apply in_list_to_in_list_append_r;
          elim (in_list_append_to_or_in_list ???? H19);autobatch]]]
      |simplify in H14;simplify;elim (remove_inlist ? ? ? H13);
       simplify in H15;elim (in_list_append_to_or_in_list ? ? ? ? H15)
       [apply in_list_to_in_list_append_l;apply H7
        [apply (in_remove ? ? ? H16 H17)
        |intro;apply H14;simplify;
         rewrite < (associative_append ? [x] (fv_Nenv l) (var_NTyp n3@n6::var_NTyp n7 @ var_NTyp n8));
         elim (in_list_append_to_or_in_list ? ? (x::fv_Nenv l) (var_NTyp n3@var_NTyp n7) H18);
         [apply in_list_to_in_list_append_l;apply H19
         |apply in_list_to_in_list_append_r;
          elim (in_list_append_to_or_in_list ???? H19);autobatch depth=4]]
       |apply in_list_to_in_list_append_r;apply in_remove;
        [elim (remove_inlist ??? H13);intro;apply H19;
         elim (swap_case a n1 n6)
         [elim H21
          [elim H14;rewrite < H22;rewrite < H20;apply in_list_head
          |autobatch paramodulation]
         |elim (remove_inlist ??? H17);elim H23;autobatch paramodulation]
        |apply H8
         [apply (in_remove ? ? ? H16);elim (remove_inlist ??? H17);assumption
         |intro;apply H14;simplify;
          rewrite < (associative_append ? [x] (fv_Nenv l) (var_NTyp n3@n6::var_NTyp n7 @ var_NTyp n8));
          elim (in_list_append_to_or_in_list ? ? (x::fv_Nenv l) (var_NTyp n3@var_NTyp n8) H18);
          [apply in_list_to_in_list_append_l;apply H19
          |apply in_list_to_in_list_append_r;
           elim (in_list_append_to_or_in_list ???? H19);autobatch depth=4]]]]]]
    |split
     [intro;apply H8;rewrite > H9;apply in_list_head
     |elim (remove_inlist ? ? ? H7);assumption]]
   |intro;autobatch depth=4
   |3,4:intro;elim H8;apply in_list_cons;autobatch depth=4]]]]
qed.
 
theorem adequacy : ∀G,T,U.NJSubtype G T U → 
                    JSubtype (encodeenv G) (encodetype T []) (encodetype U []).
intros;elim H;simplify
  [1,2,3,4:autobatch
  |apply SA_All
     [assumption
     |intros;lapply (NSA_All ? ? ? ? ? ? ? H1 H3);
      rewrite < (encode_subst n3 X n [])
        [rewrite < (encode_subst n5 X n1 [])
           [rewrite < eq_fv_Nenv_fv_env in H5;
            elim (NJS_fv_to_fvNenv ? ? ? Hletin);
            simplify in H6;simplify in H7;
            apply (H4 ? H5)
              [elim (decidable_eq_nat X n)
                 [assumption
                 |elim H5;autobatch depth=5]
              |elim (decidable_eq_nat X n1)
                 [assumption
                 |elim H5;autobatch depth=5]]
           |2,3:autobatch
           |intro;elim (NJS_fv_to_fvNenv ? ? ? Hletin);
            simplify in H8;
            elim (decidable_eq_nat X n1)
              [assumption
              |elim H5;autobatch depth=4]]
        |2,3:autobatch
        |intro;elim (NJS_fv_to_fvNenv ? ? ? Hletin);
         simplify in H7;elim (decidable_eq_nat X n)
           [assumption
           |elim H5;autobatch depth=4]]]]
qed.

let rec closed_type T n ≝
  match T with
    [ TVar m ⇒ m < n 
    | TFree X ⇒ True
    | Top ⇒ True
    | Arrow T1 T2 ⇒ closed_type T1 n ∧ closed_type T2 n
    | Forall T1 T2 ⇒  closed_type T1 n ∧ closed_type T2 (S n)].
    
lemma decoder : ∀T,n.closed_type T n → 
                     ∀l.length ? l = n → distinct_list l →
                  (\forall x. x ∈ (fv_type T) \to x ∉ l) \to   
                     ∃U.T = encodetype U l.
intro;elim T
  [simplify in H;apply (ex_intro ? ? (TName (nth ? l O n)));simplify;
   rewrite > lookup_nth;simplify;autobatch;
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
         apply (ex_intro ? ? (NArrow a a1));autobatch;
        |intros;apply H5;simplify;autobatch]
     |intros;apply H5;simplify;autobatch]
  |simplify in H2;elim H2;elim (H ? H6 ? H3 H4);elim (fresh_name (fv_type t1@l));
     [elim (H1 ? H7 (a1::l))
        [apply (ex_intro ? ? (NForall a1 a a2));simplify;autobatch
        |simplify;autobatch
        |unfold;intros;intro;apply H12;generalize in match H13;generalize in match H10;
         generalize in match H11;generalize in match H9;
         generalize in match m;generalize in match n1;
         apply nat_elim2
           [intro;elim n2
              [reflexivity
              |simplify in H18;rewrite > H18 in H9;elim H9;simplify in H16;
               lapply (le_S_S_to_le ? ? H16);autobatch depth=4]
           |intro;intros;change in H17:(? ? % ?) with (nth nat l O n2);
            simplify in H17:(? ? ? %);elim H9;rewrite < H17;
            apply in_list_to_in_list_append_r;apply nth_in_list;
            simplify in H16;autobatch
           |intros;change in H18 with (nth nat l O n2 = nth nat l O m1);
            unfold in H4;elim (decidable_eq_nat n2 m1)
              [autobatch
              |simplify in H17;simplify in H16;elim (H4 ? ? ? ? H19);autobatch]]
        |intro;elim (in_list_cons_case ? ? ? ? H11)
           [apply H9;apply in_list_to_in_list_append_l;rewrite < H12;assumption
           |apply (H5 x);simplify;autobatch]]
     |apply H5;simplify;autobatch]]
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
  [1,2:apply I
  |split;assumption
  |split
     [assumption
     |elim (fresh_name (fv_env l@fv_type t1));lapply (H4 a)
        [autobatch
        |*:intro;autobatch]]]
qed.

lemma adeq_WFE2 : ∀G1.WFEnv G1 → ∀G2.(G1 = encodeenv G2) → NWFEnv G2.
intros 2;elim H 0
  [intro;elim G2
     [apply NWFE_Empty
     |simplify in H2;destruct H2]
  |intros 9;elim G2
     [simplify in H5;destruct H5
     |elim a in H6;simplify in H6;destruct H6;apply NWFE_cons;autobatch]]
qed.

lemma in_list_encodeenv : \forall b,X,T,l.
            in_list ? (mk_bound b X (encodetype T [])) (encodeenv l) \to
            \exists U.encodetype U [] = encodetype T [] \land
                      (mk_nbound b X U) ∈ l.
intros 4;elim l
  [simplify in H;elim (not_in_list_nil ? ? H)
  |simplify in H1;inversion H1;elim a 0;simplify;intros;destruct;
     [apply (ex_intro ? ? n1);split;autobatch
     |elim (H H2);elim H4;apply (ex_intro ? ? a1);split;autobatch]]
qed.

lemma eq_swap_NTyp_to_case :
  \forall X,Y,Z,T. Y ∉ (X::var_NTyp T) \to
    swap_NTyp Z Y (swap_NTyp Y X T) = swap_NTyp Z X T \to
      Z = X \lor Z ∉ (fv_NTyp T).
intros 4;elim T
  [simplify in H;simplify in H1;elim (decidable_eq_nat X n)
     [rewrite > H2;simplify;elim (decidable_eq_nat Z n)
        [left;assumption
        |right;intro;apply H3;apply in_list_singleton_to_eq;assumption]
     |elim (decidable_eq_nat Y n)
        [elim H;autobatch;
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
                    |*:intro;autobatch]]]
           |*:intro;autobatch]]]
  |simplify;right;apply not_in_list_nil
  |elim H
     [left;assumption
     |elim H1
        [left;assumption
        |right;simplify;intro;elim (in_list_append_to_or_in_list ? ? ? ? H6)
           [elim (H4 H7)
           |elim (H5 H7)]
        |intro;apply H2;simplify;inversion H5;intros;destruct;autobatch;
        |simplify in H3;destruct H3;assumption]
     |intro;apply H2;simplify;inversion H4;intros;destruct;autobatch
     |simplify in H3;destruct H3;assumption]
  |elim H
     [left;assumption
     |elim H1
        [left;assumption
        |right;simplify;intro;elim (in_list_append_to_or_in_list ? ? ? ? H6)
           [elim (H4 H7)
           |elim H5;elim (remove_inlist ? ? ? H7);assumption]
        |intro;apply H2;simplify;inversion H5;intros;destruct;autobatch
        |simplify in H3;destruct H3;assumption]
     |intro;apply H2;simplify;inversion H4;intros;destruct;autobatch depth=4;
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
   rewrite > Hcut;apply NSA_Top;autobatch;
  |intros;cut (T2 = TName n ∧ U2 = TName n) 
   [|split
     [elim T2 in H4 0;simplify;intros;destruct;reflexivity
     |elim U2 in H5 0;simplify;intros;destruct;reflexivity]]
   elim Hcut;
   rewrite > H6;rewrite > H7;apply NSA_Refl_TVar; 
     [autobatch
     |rewrite > H3 in H2;rewrite < eq_fv_Nenv_fv_env in H2;assumption]
  |intros;cut (T2 = TName n) 
     [|elim T2 in H5 0;simplify;intros;destruct;reflexivity]
   rewrite > Hcut;elim (decoder t1 O ? []);
     [rewrite > H4 in H1;rewrite > H7 in H1;elim (in_list_encodeenv ???? H1);
      elim H8;autobatch
     |4:unfold;intros;simplify in H7;elim (not_le_Sn_O ? H7)
     |*:autobatch]
  |intros;cut (∃u,u1,u2,u3.T2 = NArrow u u1 ∧ U2 = NArrow u2 u3)
     [decompose;rewrite > H8;rewrite > H10;rewrite > H10 in H7;simplify in H7;destruct;
      simplify in H6;destruct;autobatch width=4 size=9
     |generalize in match H6;elim T2 0;simplify;intros;destruct;
      generalize in match H7;elim U2 0;simplify;intros;destruct;
      autobatch depth=6 width=2 size=7]
  |intros;cut (∃n,u,u1,n1,u2,u3.T2 = NForall n u u1 ∧ U2 = NForall n1 u2 u3)
     [decompose;rewrite > H8;rewrite > H10;
      rewrite > H8 in H6;rewrite > H10 in H7;simplify in H6;simplify in H7;
      destruct;lapply (SA_All ? ? ? ? ? H1 H3);
      lapply (JS_to_WFT1 ? ? ? Hletin);lapply (JS_to_WFT2 ? ? ? Hletin);
      apply NSA_All
        [autobatch;
        |intros;apply H4;
           [apply Z
           |2,3:autobatch
           |rewrite < (encode_subst a2 Z a []);
              [1,2,3:autobatch
              |lapply (SA_All ? ? ? ? ? H1 H3);lapply (JS_to_WFT1 ? ? ? Hletin);
               intro;elim (decidable_eq_nat Z a)
                 [assumption
                 |lapply (fv_WFT ? Z ? Hletin1)
                    [elim H5;autobatch
                    |simplify;apply in_list_to_in_list_append_r;
                     apply fv_NTyp_fv_Typ
                       [assumption
                       |intro;autobatch]]]]
           |rewrite < (encode_subst a5 Z a3 [])
              [1,2,3:autobatch
              |intro;elim H7;autobatch]]]
     |generalize in match H6;elim T2 0;simplify;intros;destruct;
      generalize in match H7;elim U2 0;simplify;intros;destruct;
      autobatch depth=8 width=2 size=9]]
qed.

theorem NJS_trans : ∀G,T,U,V.NJSubtype G T U → NJSubtype G U V → NJSubtype G T V.
intros;apply faithfulness [5,6,7:autobatch|4:autobatch|*:skip]
qed.
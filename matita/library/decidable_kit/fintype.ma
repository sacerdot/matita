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

include "decidable_kit/eqtype.ma".
include "decidable_kit/list_aux.ma".

record finType : Type ≝ {
  fsort :> eqType;
  enum : list fsort;
  enum_uniq : ∀x:fsort. count fsort (cmp fsort x) enum = (S O)  
}.

definition segment : nat → eqType ≝ 
  λn.sub_eqType nat_eqType (λx:nat_eqType.ltb x n).

definition is_some : ∀d:eqType. option d → bool ≝ 
  λd:eqType.λo:option d.notb (cmp (option_eqType d) (None ?) o).

definition filter ≝
  λA,B:Type.λp:A→option B.λl:list A.
  foldr A ? 
    (λx,acc. match (p x) with [None ⇒ acc | (Some y) ⇒ cons B y acc]) (nil B) l.

definition segment_enum  ≝
  λbound.filter ? ? (if_p nat_eqType (λx.ltb x bound)) (iota O bound).

lemma iota_ltb : ∀x,p:nat. mem nat_eqType x (iota O p) = ltb x p.
intros (x p); elim p; simplify;[reflexivity] 
apply (cmpP nat_eqType x n); intros (E); rewrite > H; clear H; simplify;
[1: symmetry; apply (p2bT ? ? (lebP ? ?)); rewrite > E; apply le_n;
|2: rewrite < (leb_eqb x n); rewrite > E; reflexivity;]
qed.

lemma mem_filter :
  ∀d1,d2:eqType.∀x:d2.∀l:list d1.∀p:d1 → option d2.
  (∀y.mem d1 y l = true → 
    match (p y) with [None ⇒ false | (Some q) ⇒ cmp d2 x q] = false) →
  mem d2 x (filter d1 d2 p l) = false.
intros 5 (d1 d2 x l p); 
elim l; simplify; [reflexivity]
generalize in match (refl_eq ? (p a));
generalize in match (p a) in ⊢ (? ? ? % → %); intros 1 (b); cases b; clear b; intros (Hpt);
[1: apply H; intros (y Hyl);
    apply H1; simplify; 
    rewrite > Hyl; rewrite > orbC; reflexivity;
|2: simplify; apply (cmpP d2 x s); simplify; intros (E);
    [1: rewrite < (H1 a); simplify; [rewrite > Hpt; rewrite > E]
        simplify; rewrite > cmp_refl; reflexivity
    |2: apply H; intros; apply H1; simplify; rewrite > H2;
        rewrite > orbC; reflexivity]]
qed.
  
lemma count_O : 
  ∀d:eqType.∀p:d→bool.∀l:list d. 
    (∀x:d.mem d x l = true → notb (p x) = true) → count d p l = O.
intros 3 (d p l); elim l; simplify; [1: reflexivity]
generalize in match (refl_eq ? (p a));
generalize in match (p a) in ⊢ (? ? ? % → %); intros 1 (b);
cases b; simplify; 
[2:intros (Hpt); apply H; intros; apply H1; simplify;
   apply (cmpP d x a); [2: rewrite > H2;]; intros; reflexivity;
|1:intros (H2); lapply (H1 a); [2:simplify; rewrite > cmp_refl; simplify; autobatch]
   rewrite > H2 in Hletin; simplify in Hletin; destruct Hletin]
qed.    
    
lemma segment_finType : nat → finType.
intros (bound); 
letin fsort ≝ (segment bound);
letin enum ≝ (segment_enum bound);
cut (∀x:fsort. count fsort (cmp fsort x) enum = (S O));
 [ apply (mk_finType fsort enum Hcut)
 | intros (x); cases x (n Hn); simplify in Hn; clear x;
   generalize in match Hn; generalize in match Hn; clear Hn;
   unfold enum;
   unfold segment_enum;
   generalize in match bound in ⊢ (% → ? → ? ? (? ? ? (? ? ? ? %)) ?);
   intros 1 (m); elim m  (Hm Hn p IH Hm Hn); [ simplify in Hm; destruct Hm ]
   simplify; cases (eqP bool_eqType (ltb p bound) true); simplify;
   [1:unfold fsort;
      unfold segment in ⊢ (? ? match ? % ? ? with [_ ⇒ ?|_ ⇒ ?] ?);
      unfold nat_eqType in ⊢ (? ? match % with [_ ⇒ ?|_ ⇒ ?] ?);
      simplify; apply (cmpP nat_eqType n p); intros (Enp); simplify;
      [2:rewrite > IH; [1,3: autobatch]
         rewrite <  ltb_n_Sm in Hm; rewrite > Enp in Hm;
         rewrite > orbC in Hm; assumption;
      |1:clear IH; rewrite > (count_O fsort); [reflexivity]
         intros 1 (x); rewrite < Enp; cases x (y Hy); 
         intros (ABS); clear x; unfold segment; unfold notb; simplify;
         apply (cmpP ? n y); intros (Eny); simplify; [2:reflexivity]
         rewrite < ABS; symmetry; clear ABS;
         generalize in match Hy; clear Hy;rewrite < Eny;
         simplify; intros (Hn); apply (mem_filter nat_eqType fsort); intros (w Hw);
         fold simplify (sort nat_eqType); (* CANONICAL?! *)
         cases (in_sub_eq nat_eqType (λx:nat_eqType.ltb x bound) w);
         simplify; [2: reflexivity]
         generalize in match H1; clear H1; cases s (r Pr); clear s; intros (H1);
         unfold fsort; unfold segment; simplify; simplify in H1; rewrite > H1;
         rewrite > iota_ltb in Hw; apply (p2bF ? ? (eqP nat_eqType ? ?));
         unfold Not; intros (Enw); rewrite > Enw in Hw; 
         rewrite > ltb_refl in Hw; destruct Hw]
   |2:rewrite > IH; [1:reflexivity|3:assumption]
      rewrite <  ltb_n_Sm in Hm;
      cases (b2pT ? ?(orbP ? ?) Hm);[1: assumption]
      rewrite > (b2pT ? ? (eqbP ? ?) H1) in Hn;
      rewrite > Hn in H; cases (H ?); reflexivity]]
qed.

let rec uniq (d:eqType) (l:list d) on l : bool ≝
  match l with 
  [ nil ⇒ true 
  | (cons x tl) ⇒ andb (notb (mem d x tl)) (uniq d tl)].

lemma uniq_mem : ∀d:eqType.∀x:d.∀l:list d.uniq d (x::l) = true → mem d x l = false.
intros (d x l H); simplify in H; lapply (b2pT ? ? (andbP ? ?) H) as H1; clear H;
cases H1 (H2 H3); lapply (b2pT ? ?(negbP ?) H2); assumption;
qed.

lemma andbA : ∀a,b,c.andb a (andb b c) = andb (andb a b) c.
intros; cases a; cases b; cases c; reflexivity; qed.

lemma andbC : ∀a,b. andb a b = andb b a.
intros; cases a; cases b; reflexivity; qed.

lemma uniq_tail : 
  ∀d:eqType.∀x:d.∀l:list d. uniq d (x::l) = andb (negb (mem d x l)) (uniq d l).
intros (d x l); elim l; simplify; [reflexivity]
apply (cmpP d x a); intros (E); simplify ; try rewrite > E; [reflexivity]
rewrite > andbA; rewrite > andbC in ⊢ (? ? (? % ?) ?); rewrite < andbA;
rewrite < H; rewrite > andbC in ⊢ (? ? ? (? % ?)); rewrite < andbA; reflexivity;
qed.
  
lemma count_O_mem : ∀d:eqType.∀x:d.∀l:list d.ltb O (count d (cmp d x) l) = mem d x l.
intros 3 (d x l); elim l [reflexivity] simplify; rewrite < H; cases (cmp d x a);
reflexivity; qed.
  
lemma uniqP : ∀d:eqType.∀l:list d. 
  reflect (∀x:d.mem d x l = true → count d (cmp d x) l = (S O)) (uniq d l).
intros (d l); apply prove_reflect; elim l; [1: simplify in H1; destruct H1 | 3: simplify in H; destruct H]
[1: generalize in match H2; simplify in H2; 
    lapply (b2pT ? ? (orbP ? ?) H2) as H3; clear H2; 
    cases H3; clear H3; intros;
    [2: lapply (uniq_mem ? ? ? H1) as H4; simplify; apply (cmpP d x a);  
        intros (H5); simplify;
        [1: rewrite > count_O; [reflexivity]
            intros (y Hy); rewrite > H5 in H2 H3 ⊢ %; clear H5; clear x; 
            rewrite > H2 in H4; destruct H4;
         |2: simplify; apply H; 
             rewrite > uniq_tail in H1; cases (b2pT ? ? (andbP ? ?) H1); 
             assumption;]
    |1: simplify; rewrite > H2; simplify; rewrite > count_O; [reflexivity]
        intros (y Hy); rewrite > (b2pT ? ? (eqP d ? ?) H2) in H3 ⊢ %;
        clear H2; clear x; lapply (uniq_mem ? ? ? H1) as H4;
        apply (cmpP d a y); intros (E); [2: reflexivity].
        rewrite > E in H4; rewrite > H4 in Hy; destruct Hy;]
|2: rewrite > uniq_tail in H1; 
    generalize in match (refl_eq ? (uniq d l1));
    generalize in match (uniq d l1) in ⊢ (? ? ? % → %); intros 1 (b); cases b; clear b;
    [1: intros (E); rewrite > E in H1; rewrite > andbC in H1; simplify in H1;
        unfold Not; intros (A); lapply (A a) as A'; 
        [1: simplify in A'; rewrite > cmp_refl in A'; simplify in A';
            destruct A'; rewrite < count_O_mem in H1;
            rewrite > Hcut in H1; simplify in H1; destruct H1;  
        |2: simplify; rewrite > cmp_refl; reflexivity;]
    |2: intros (Ul1); lapply (H Ul1); unfold Not; intros (A); apply Hletin;
        intros (r Mrl1); lapply (A r); 
          [2: simplify; rewrite > Mrl1; cases (cmp d r a); reflexivity]
        generalize in match Hletin1; simplify; apply (cmpP d r a); 
        simplify; intros (E Hc); [2: assumption]
        destruct Hc; rewrite < count_O_mem in Mrl1;
        rewrite > Hcut in Mrl1; simplify in Mrl1; destruct Mrl1;]]
qed.
    
lemma mem_finType : ∀d:finType.∀x:d. mem d x (enum d) = true. 
intros 1 (d); cases d; simplify; intros; rewrite < count_O_mem;
rewrite > H; reflexivity;
qed.

lemma uniq_fintype_enum :  ∀d:finType. uniq d (enum d) = true.
intros; cases d; simplify; apply (p2bT ? ? (uniqP ? ?)); intros; apply H;
qed.

lemma sub_enumP : ∀d:finType.∀p:d→bool.∀x:sub_eqType d p. 
  count (sub_eqType d p) (cmp ? x) (filter ? ? (if_p ? p) (enum d)) = (S O).
intros (d p x); cases x (t Ht); clear x;
generalize in match (mem_finType d t); 
generalize in match (uniq_fintype_enum d); 
elim (enum d); [simplify in H1; destruct H1] simplify;  
cases (in_sub_eq d p a); simplify; 
[1:generalize in match H3; clear H3; cases s (r Hr); clear s;
   simplify; intros (Ert1); generalize in match Hr; clear Hr;
   rewrite > Ert1; clear Ert1; clear r; intros (Ht1);
   unfold  sub_eqType in ⊢ (? ? match ? (% ? ?) ? ? with [_ ⇒ ?|_ ⇒ ?] ?); 
   simplify; apply (cmpP ? t a); simplify; intros (Ett1);
   [1: cut (count (sub_eqType d p) (cmp (sub_eqType d p) {t,Ht})
            (filter d (sigma d p) (if_p d p) l) = O); [1:rewrite > Hcut; reflexivity]
       lapply (uniq_mem ? ? ? H1);
       generalize in match Ht; 
       rewrite > Ett1; intros (Ht1'); clear Ht1;
       generalize in match Hletin; elim l; [ reflexivity]
       simplify; cases (in_sub_eq d p a1); simplify; 
       [1: generalize in match H5; cases s; simplify; intros; clear H5; 
           unfold sub_eqType in ⊢ (? ? match ? (% ? ?) ? ? with [_ ⇒ ?|_ ⇒ ?] ?);
           simplify; rewrite > H7; simplify in H4;
           generalize in match H4; clear H4; apply (cmpP ? a a1);
           simplify; intros; [destruct H5] apply H3; assumption;
       |2: apply H3;
           generalize in match H4; clear H4; simplify; apply (cmpP ? a a1);
           simplify; intros; [destruct H6] assumption;]
   |2: apply H; [ rewrite > uniq_tail in H1; cases (b2pT ? ? (andbP ? ?) H1); assumption]
       simplify in H2; rewrite > Ett1 in H2; simplify in H2; assumption] 
|2:rewrite > H; [1:reflexivity|2: rewrite > uniq_tail in H1; cases (b2pT ? ? (andbP ? ?) H1); assumption]
   simplify in H2; generalize in match H2; apply (cmpP ? t a); 
   intros (E) [2:assumption] clear H; rewrite > E in Ht; rewrite > H3 in Ht;
   destruct Ht;]
qed.
 
definition sub_finType : ∀d:finType.∀p:d→bool.finType ≝
  λd:finType.λp:d→bool. mk_finType (sub_eqType d p) (filter ? ? (if_p ? p) (enum d)) (sub_enumP d p).
 

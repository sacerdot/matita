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

set "baseuri" "cic:/matita/decidable_kit/fintype/".

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
intros (x p); elim p; simplify; [1:reflexivity]
rewrite < leb_eqb;
generalize in match (refl_eq ? (cmp ? x n));
generalize in match (cmp ? x n) in ⊢ (? ? % ? → %); intros 1 (b);
cases b; simplify; intros (H1); [1: reflexivity]
rewrite > H; fold simplify (ltb x n); rewrite > H1; reflexivity;
qed.

lemma mem_filter :
  ∀d1,d2:eqType.(*∀y:d1.*)∀x:d2.∀l:list d1.∀p:d1 → option d2.
  (∀y.mem d1 y l = true → 
    match (p y) with [None ⇒ false | (Some q) ⇒ cmp d2 x q] = false) →
  mem d2 x (filter d1 d2 p l) = false.
intros 5 (d1 d2 x l p); 
elim l; [1: simplify; auto]
simplify; fold simplify (filter d1 d2 p l1);
generalize in match (refl_eq ? (p t));
generalize in match (p t) in ⊢ (? ? ? % → %); intros 1 (b); cases b; clear b;
[1: simplify; intros (Hpt); apply H; intros (y Hyl);
  apply H1; simplify; fold simplify (orb (cmp ? y t) (mem ? y l1));
  rewrite > Hyl; rewrite > orbC; reflexivity;
|2:simplify; intros (Hpt); 
  generalize in match (refl_eq ? (cmp ? x s));
  generalize in match (cmp ? x s) in ⊢ (? ? ? % → %); intros 1 (b); cases b; clear b;
  [1: simplify; intros (Exs);
      rewrite < (H1 t); [2: simplify; rewrite > cmp_refl; reflexivity;]
      rewrite > Hpt; simplify; symmetry; assumption;
  |2: intros (Dxs); simplify; apply H; intros;
      apply H1; simplify; fold simplify (orb (cmp ? y t) (mem ? y l1));
      rewrite > H2; rewrite > orbC; reflexivity;]]
qed.
  
lemma count_O : 
  ∀d:eqType.∀p:d→bool.∀l:list d. 
    (∀x:d.mem d x l = true → notb (p x) = true) → count d p l = O.
intros 3 (d p l); elim l; simplify; [1: reflexivity]
fold simplify (count d p l1); (* XXX simplify troppo *)
generalize in match (refl_eq ? (p t));
generalize in match (p t) in ⊢ (? ? ? % → %); intros 1 (b);
cases b; simplify; 
[2:intros (Hpt); apply H; intros; apply H1; simplify;
   generalize in match (refl_eq ? (cmp d x t));
   generalize in match (cmp d x t) in ⊢ (? ? ? % → %); intros 1 (b1);
   cases b1; simplify; intros; [2:rewrite > H2] auto.
|1:intros (H2); lapply (H1 t); [2:simplify; rewrite > cmp_refl; simplify; auto]
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
   unfold segment_enum;
   generalize in match bound in ⊢ (% → ? → ? ? (? ? ? (? ? ? ? %)) ?);
   intros 1 (m); elim m  (Hm Hn p IH Hm Hn);
   [ destruct Hm;
   | simplify; cases (eqP bool_eqType (ltb p bound) true); simplify;
     (* XXX simplify che spacca troppo *)
     fold simplify (filter nat_eqType (sigma nat_eqType (λx.ltb x bound))
                     (if_p nat_eqType (λx.ltb x bound)) (iota O p));
     [1:unfold segment in ⊢ (? ? match ? % ? ? with [true⇒ ?|false⇒ ?] ?);
        unfold nat_eqType in ⊢ (? ? match % with [true⇒ ?|false⇒ ?] ?);
        simplify in ⊢ (? ? match % with [true⇒ ?|false⇒ ?] ?);
        generalize in match (refl_eq ? (eqb n p));
        generalize in match (eqb n p) in ⊢ (? ? ? % → %); intros 1(b);
        cases b; simplify;
        [2:intros (Enp); rewrite > IH; [1,3: auto]
           rewrite <  ltb_n_Sm in Hm; rewrite > Enp in Hm;
           generalize in match Hm; cases (ltb n p); intros; [1:reflexivity]
           simplify in H1; destruct H1;
        |1:clear IH; intros (Enp); 
           fold simplify (count fsort (cmp fsort {n, Hn})
                           (filter ? (sigma nat_eqType (λx.ltb x bound))
                           (if_p nat_eqType (λx.ltb x bound)) (iota O p)));
           rewrite > (count_O fsort); [1: reflexivity]
           intros 1 (x);
           rewrite < (b2pT ? ? (eqP ? n ?) Enp);
           cases x (y Hy); intros (ABS); clear x;
           unfold segment; unfold notb; simplify; 
           generalize in match (refl_eq ? (cmp ? n y));
           generalize in match (cmp ? n y) in ⊢ (? ? ? % → %); intros 1 (b); cases b; clear b;
           intros (Eny); simplify; [2: auto]
           rewrite < ABS; symmetry; clear ABS;
           generalize in match Hy; clear Hy; rewrite < (b2pT ? ? (eqP nat_eqType ? ?) Eny);
           simplify; intros (Hn); fold simplify (iota O n);
           apply (mem_filter nat_eqType fsort);
           intros (w Hw);
           fold simplify (sort nat_eqType);
           cases (in_sub_eq nat_eqType (λx:nat_eqType.ltb x bound) w);
           simplify; [2: reflexivity]
           generalize in match H1; clear H1; cases s; clear s; intros (H1);
           unfold segment; simplify; simplify in H1; rewrite > H1;
           rewrite > iota_ltb in Hw;
           apply (p2bF ? ? (eqP nat_eqType ? ?));
           unfold Not; intros (Enw);
           rewrite > Enw in Hw; rewrite > ltb_refl in Hw; destruct Hw]
     |2:rewrite > IH; [1:reflexivity|3:assumption]
          rewrite <  ltb_n_Sm in Hm;
          cases (b2pT ? ?(orbP ? ?) Hm);[1: assumption]
          rewrite > (b2pT ? ? (eqbP ? ?) H1) in Hn;
          rewrite > Hn in H; cases (H ?); reflexivity;
     ]]]      
qed.

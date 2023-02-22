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

(* classical connectives for decidable properties *)

include "decidable_kit/streicher.ma".
include "datatypes/bool.ma".
include "logic/connectives.ma".
include "nat/compare.ma".
 
(* se non includi connectives accade un errore in modo reproducibile*)

(* ### Prop <-> bool reflection predicate and lemmas for switching ### *)
inductive reflect (P : Prop) : bool  → Type ≝
  | reflect_true : P → reflect P true
  | reflect_false: ¬P → reflect P false.
  
lemma b2pT : ∀P,b. reflect P b → b = true → P.
intros 3 (P b H); 
(* XXX generalize in match H; clear H; rewrite > Db;*)
(* la rewrite pare non andare se non faccio la generalize *)
(* non va inversion: intros (H);inversion H; *)
cases H; [intros; assumption | intros 1 (ABS); destruct ABS ]
qed.

lemma b2pF : ∀P,b. reflect P b → b = false → ¬P.
intros 3 (P b H); 
cases H; [intros 1 (ABS); destruct ABS| intros; assumption]
qed.

lemma p2bT : ∀P,b. reflect P b → P → b = true.
intros 4 (P b H Hp);
cases H (Ht Hf); [ intros; reflexivity | cases (Hf Hp)]
qed.

lemma p2bF : ∀P,b. reflect P b → ¬P → b = false.
intros 4 (P b H Hp);
cases H (Ht Hf); [ cases (Hp Ht) | reflexivity ]
qed.

lemma idP : ∀b:bool.reflect (b=true) b.
intros (b); cases b; [ constructor 1; reflexivity | constructor 2;]
unfold Not; intros (H); destruct H;
qed.

lemma prove_reflect : ∀P:Prop.∀b:bool.
  (b = true → P) → (b = false → ¬P) → reflect P b.
intros 2 (P b); cases b; intros; [left|right] [autobatch.|autobatch;]
qed.   
  
(* ### standard connectives/relations with reflection predicate ### *)

definition negb : bool → bool ≝ λb.match b with [ true ⇒ false | false ⇒ true].

lemma negbP : ∀b:bool.reflect (b = false) (negb b).
intros (b); cases b; simplify; [apply reflect_false | apply reflect_true]
[unfold Not; intros (H); destruct H | reflexivity]
qed.  

definition andb : bool → bool → bool ≝
  λa,b:bool. match a with [ true ⇒ b | false ⇒ false ].
  
lemma andbP : ∀a,b:bool. reflect (a = true ∧ b = true) (andb a b).
intros (a b); apply prove_reflect; cases a; cases b; simplify; intros (H);
[1,2,3,4: rewrite > H; split; reflexivity;
|5,6,7,8: unfold Not; intros (H1); cases H1; 
          [destruct H|destruct H3|destruct H2|destruct H2]]
qed.

lemma andbPF : ∀a,b:bool. reflect (a = false ∨ b = false) (negb (andb a b)).
intros (a b); apply prove_reflect; cases a; cases b; simplify; intros (H);
[1,2,3,4: try rewrite > H; [1,2:right|3,4:left] reflexivity
|5,6,7,8: unfold Not; intros (H1); [2,3,4: destruct H]; cases H1; destruct H2]
qed.

definition orb : bool → bool → bool ≝
  λa,b.match a in bool with [true ⇒ true | false ⇒ b].
  
lemma orbP : ∀a,b:bool. reflect (a = true ∨ b = true) (orb a b).
intros (a b); cases a; cases b; simplify;
[1,2,3: apply reflect_true; [1,2: left | right ]; reflexivity 
| apply reflect_false; unfold Not; intros (H); cases H (E E); destruct E]
qed. 

lemma orbC : ∀a,b. orb a b = orb b a.
intros (a b); cases a; cases b; autobatch. qed.

lemma lebP: ∀x,y. reflect (x ≤ y) (leb x y).
intros (x y); generalize in match (leb_to_Prop x y); 
cases (leb x y); simplify; intros (H); 
[apply reflect_true | apply reflect_false ] assumption.
qed. 

lemma leb_refl : ∀n.leb n n = true.
intros (n); apply (p2bT ? ? (lebP ? ?)); apply le_n; qed.

lemma lebW : ∀n,m. leb (S n) m = true → leb n m = true.
intros (n m H); lapply (b2pT ? ? (lebP ? ?) H); clear H;
apply (p2bT ? ? (lebP ? ?)); apply lt_to_le; assumption.
qed. 

definition ltb ≝ λx,y.leb (S x) y.

lemma ltbP: ∀x,y. reflect (x < y) (ltb x y). 
intros (x y); apply (lebP (S x) y);
qed.

lemma ltb_refl : ∀n.ltb n n = false.
intros (n); apply (p2bF ? ? (ltbP ? ?)); autobatch; 
qed.
    
(* ### = between booleans as <-> in Prop ### *)    
lemma eq_to_bool : 
  ∀a,b:bool. a = b → (a = true → b = true) ∧ (b = true → a = true).
intros (a b Eab); split; rewrite > Eab; intros; assumption;
qed.
 
lemma bool_to_eq : 
  ∀a,b:bool. (a = true → b = true) ∧ (b = true → a = true) → a = b.
intros (a b Eab); decompose;
generalize in match H; generalize in match H1; clear H; clear H1;
cases a; cases b; intros (H1 H2);
[2: rewrite > (H2 ?) | 3: rewrite > (H1 ?)] reflexivity;
qed.


lemma leb_eqb : ∀n,m. orb (eqb n m) (leb (S n) m) = leb n m.
intros (n m); apply bool_to_eq; split; intros (H);
[1:cases (b2pT ? ? (orbP ? ?) H); [2: (*autobatch type;*) apply lebW; assumption; ] 
   rewrite > (eqb_true_to_eq ? ? H1); autobatch
|2:cases (b2pT ? ? (lebP ? ?) H); 
   [ elim n; [reflexivity|assumption] 
   | simplify; rewrite > (p2bT ? ? (lebP ? ?) H1); rewrite > orbC ]
   reflexivity]
qed.


(* OUT OF PLACE *)
lemma ltW : ∀n,m. n < m → n < (S m).
intros; unfold lt; unfold lt in H; autobatch. qed.

lemma ltbW : ∀n,m. ltb n m = true → ltb n (S m) = true.
intros (n m H); letin H1 ≝ (b2pT ? ? (ltbP ? ?) H); clearbody H1;
apply (p2bT ? ? (ltbP ? ?) (ltW ? ? H1));
qed.

lemma ltS : ∀n,m.n < m → S n < S m.
intros (n m H); apply (b2pT ? ? (ltbP ? ?)); simplify; apply (p2bT ? ? (ltbP ? ?) H);
qed.

lemma ltS' : ∀n,m.S n < S m → n < m.
intros (n m H); apply (b2pT ? ? (ltbP ? ?)); simplify; apply (p2bT ? ? (ltbP ? ?) H);
qed.

lemma ltb_n_Sm : ∀m.∀n:nat. (orb (ltb n m) (eqb n m)) = ltb n (S m).
intros (m n); apply bool_to_eq; split;
[1: intros; cases (b2pT ? ? (orbP ? ?) H); [1: apply ltbW; assumption]
    rewrite > (eqb_true_to_eq ? ? H1); simplify; 
    rewrite > leb_refl; reflexivity  
|2: elim n in m ⊢ % 0;
    [1: simplify; intros; cases n1; reflexivity;
    |2: intros 1 (m); elim m 0;
        [1: intros; apply (p2bT ? ? (orbP ? ?));
            lapply (H (pred n1) ?); [1: reflexivity] clear H;
            generalize in match H1; 
            generalize in match Hletin;
            cases n1; [1: simplify; intros; destruct H2]
            intros; unfold pred in H; simplify in H;
            cases (b2pT ? ? (orbP ? ?) H); [left|right] assumption; 
        |2: clear m; intros (m IH1 IH2 w);
            lapply (IH1 ? (pred w));
            [3: generalize in match H; cases w; [2: intros; assumption]
                simplify; intros; destruct H1;
            |1: intros; apply (IH2 (S n1)); assumption;
            |2: generalize in match H; generalize in match Hletin; 
                cases w; [1: simplify; intros; destruct H2]
                intros (H H1); cases (b2pT ? ? (orbP ? ?) H);
                apply (p2bT ? ? (orbP ? ?));[left|right] assumption]]]]
qed.
        
(* non mi e' chiaro a cosa serva ... *)
lemma congr_S : ∀n,m.n = m → S n = S m.
intros 1; cases n; intros; rewrite > H; reflexivity.
qed.

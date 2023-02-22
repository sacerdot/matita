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
include "nat/compare.ma".
include "list/list.ma".
include "list/in.ma".

(*** useful definitions and lemmas not really related to Fsub ***)

definition max \def 
\lambda m,n.
  match (leb m n) with
     [true \Rightarrow n
     |false \Rightarrow m]. 
     
lemma le_n_max_m_n: \forall m,n:nat. n \le max m n.
intros.
unfold max.
apply (leb_elim m n)
  [simplify.intros.apply le_n
  |simplify.intros.autobatch
  ]
qed.
  
lemma le_m_max_m_n: \forall m,n:nat. m \le max m n.
intros.
unfold max.
apply (leb_elim m n)
  [simplify.intro.assumption
  |simplify.intros.autobatch
  ]
qed.  

lemma max_case : \forall m,n.(max m n) = match (leb m n) with
      [ true \Rightarrow n
      | false \Rightarrow m ].
intros;elim m;simplify;reflexivity;
qed.

definition swap : nat → nat → nat → nat ≝
  λu,v,x.match (eqb x u) with
    [true ⇒ v
    |false ⇒ match (eqb x v) with
       [true ⇒ u
       |false ⇒ x]].
       
lemma swap_left : ∀x,y.(swap x y x) = y.
intros;unfold swap;rewrite > eqb_n_n;simplify;reflexivity;
qed.

lemma swap_right : ∀x,y.(swap x y y) = x.
intros;unfold swap;rewrite > eqb_n_n;apply (eqb_elim y x);intro;autobatch;
qed.

lemma swap_other : \forall x,y,z.(z \neq x) \to (z \neq y) \to (swap x y z) = z.
intros;unfold swap;apply (eqb_elim z x);intro;simplify
  [elim H;assumption
  |rewrite > not_eq_to_eqb_false;autobatch]
qed.

lemma swap_inv : \forall u,v,x.(swap u v (swap u v x)) = x.
intros;unfold in match (swap u v x);apply (eqb_elim x u);intro;simplify
  [autobatch paramodulation
  |apply (eqb_elim x v);intro;simplify
     [autobatch paramodulation
     |apply swap_other;assumption]]
qed.

lemma swap_inj : ∀u,v,x,y.swap u v x = swap u v y → x = y.
intros 4;unfold swap;apply (eqb_elim x u);simplify;intro
  [apply (eqb_elim y u);simplify;intro
     [intro;autobatch paramodulation
     |apply (eqb_elim y v);simplify;intros
        [autobatch paramodulation
        |elim H2;symmetry;assumption]]
  |apply (eqb_elim y u);simplify;intro
     [apply (eqb_elim x v);simplify;intros;
        [autobatch paramodulation
        |elim H2;assumption]
     |apply (eqb_elim x v);simplify;intro
        [apply (eqb_elim y v);simplify;intros
           [autobatch paramodulation
           |elim H1;symmetry;assumption]
        |apply (eqb_elim y v);simplify;intros
           [elim H;assumption
           |assumption]]]]
qed.

definition swap_list : nat \to nat \to (list nat) \to (list nat) ≝
  \lambda u,v,l.(map ? ? (swap u v) l). 

let rec posn l x on l ≝
  match l with
  [ nil ⇒ O
  | (cons (y:nat) l2) ⇒
      match (eqb x y) with
            [ true ⇒ O
            | false ⇒ S (posn l2 x)]].
            
let rec lookup n l on l ≝
  match l with
    [ nil ⇒ false
    | cons (x:nat) l1 ⇒ match (eqb n x) with
              [true ⇒ true
              |false ⇒ (lookup n l1)]]. 
                             
let rec head (A:Type) l on l ≝
  match l with
  [ nil ⇒ None A
  | (cons (x:A) l2) ⇒ Some A x].

definition max_list : (list nat) \to nat \def
  \lambda l.let rec aux l0 m on l0 \def
    match l0 with
      [ nil ⇒ m
      | (cons n l2) ⇒ (aux l2 (max m n))]
    in aux l O.

let rec remove_nat (x:nat) (l:list nat) on l \def
  match l with
  [ nil ⇒ (nil nat) 
  | (cons y l2) ⇒ match (eqb x y) with
                  [ true ⇒ (remove_nat x l2)
                  | false ⇒ (y :: (remove_nat x l2)) ]].
                  
lemma in_lookup : \forall x,l.x ∈ l \to (lookup x l = true).
intros;elim H;simplify
  [rewrite > eqb_n_n;reflexivity
  |rewrite > H2;elim (eqb a a1);reflexivity]
qed.

lemma lookup_in : \forall x,l.(lookup x l = true) \to x ∈ l.
intros 2;elim l
  [simplify in H;destruct H
  |generalize in match H1;simplify;elim (decidable_eq_nat x a)
     [applyS in_list_head
     |apply in_list_cons;apply H;
      rewrite > (not_eq_to_eqb_false ? ? H2) in H3;simplify in H3;assumption]]
qed.

lemma posn_length : \forall x,vars.x ∈ vars → 
                       (posn vars x) < (length ? vars).
intros 2;elim vars
  [elim (not_in_list_nil ? ? H)
  |inversion H1;intros;destruct;simplify
     [rewrite > eqb_n_n;simplify;
      apply lt_O_S
     |elim (eqb x a);simplify
        [apply lt_O_S
        |apply le_S_S;apply H;assumption]]]
qed.

lemma in_remove : \forall a,b,l.(a ≠ b) \to a ∈ l \to
                                a ∈ (remove_nat b l).
intros 4;elim l
  [elim (not_in_list_nil ? ? H1)
  |inversion H2;intros;destruct;simplify
     [rewrite > not_eq_to_eqb_false
        [simplify;apply in_list_head
        |intro;apply H;symmetry;assumption]
     |elim (eqb b a1);simplify
        [apply H1;assumption
        |apply in_list_cons;apply H1;assumption]]]
qed.

lemma swap_same : \forall x,y.swap x x y = y.
intros;elim (decidable_eq_nat y x)
  [autobatch paramodulation
  |rewrite > swap_other;autobatch]
qed.

lemma not_nat_in_to_lookup_false : ∀l,X. X ∉ l → lookup X l = false.
intros 2;elim l;simplify
  [reflexivity
  |elim (decidable_eq_nat X a)
     [elim H1;rewrite > H2;apply in_list_head
     |rewrite > (not_eq_to_eqb_false ? ? H2);simplify;apply H;intro;apply H1;
      apply (in_list_cons ? ? ? ? H3);]]
qed.

lemma lookup_swap : ∀a,b,x,vars.
                    lookup (swap a b x) (swap_list a b vars) =
                    lookup x vars.
intros 4;elim vars;simplify
  [reflexivity
  |elim (decidable_eq_nat x a1)
     [rewrite > H1;rewrite > eqb_n_n;rewrite > eqb_n_n;simplify;reflexivity
     |rewrite > (not_eq_to_eqb_false ? ? H1);elim (decidable_eq_nat x a)
        [rewrite > H;rewrite > H2;rewrite > swap_left;
         elim (decidable_eq_nat b a1)
           [rewrite < H3;rewrite > swap_right;
            rewrite > (not_eq_to_eqb_false b a)
              [reflexivity
              |intro;autobatch]
           |rewrite > (swap_other a b a1)
              [rewrite > (not_eq_to_eqb_false ? ? H3);simplify;reflexivity
              |*:intro;autobatch]]
        |elim (decidable_eq_nat x b)
           [rewrite > H;rewrite > H3;rewrite > swap_right;
            elim (decidable_eq_nat a1 a)
              [rewrite > H4;rewrite > swap_left;
               rewrite > (not_eq_to_eqb_false a b)
                 [reflexivity
                 |intro;autobatch]
              |rewrite > (swap_other a b a1)
                 [rewrite > (not_eq_to_eqb_false a a1)
                    [reflexivity
                    |intro;autobatch]
                 |assumption
                 |intro;autobatch]]
           |rewrite > H;rewrite > (swap_other a b x)
              [elim (decidable_eq_nat a a1)
                 [rewrite > H4;rewrite > swap_left;
                  rewrite > (not_eq_to_eqb_false ? ? H3);reflexivity
                 |elim (decidable_eq_nat b a1)
                    [rewrite > H5;rewrite > swap_right;
                     rewrite > (not_eq_to_eqb_false ? ? H2);reflexivity
                    |rewrite > (swap_other a b a1)
                       [rewrite > (not_eq_to_eqb_false ? ? H1);reflexivity
                       |*:intro;autobatch]]]
              |*:assumption]]]]]
qed.

lemma posn_swap : ∀a,b,x,vars.
                  posn vars x = posn (swap_list a b vars) (swap a b x).
intros 4;elim vars;simplify
  [reflexivity
  |rewrite < H;elim (decidable_eq_nat x a1)
     [rewrite > H1;do 2 rewrite > eqb_n_n;reflexivity
     |elim (decidable_eq_nat (swap a b x) (swap a b a1))
        [elim H1;autobatch
        |rewrite > (not_eq_to_eqb_false ? ? H1);
         rewrite > (not_eq_to_eqb_false ? ? H2);reflexivity]]]
qed.

lemma remove_inlist : \forall x,y,l.x ∈ (remove_nat y l) → x ∈ l \land x ≠ y.
intros 3;elim l 0;simplify;intro
  [elim (not_in_list_nil ? ? H)
  |elim (decidable_eq_nat y a)
     [rewrite > H in H2;rewrite > eqb_n_n in H2;simplify in H2;
      rewrite > H in H1;elim (H1 H2);rewrite > H;split
        [apply in_list_cons;assumption
        |assumption]
     |rewrite > (not_eq_to_eqb_false ? ? H) in H2;simplify in H2;
      inversion H2;intros;destruct;
        [split;autobatch
        |elim (H1 H3);split;autobatch]]]
qed.

lemma inlist_remove : ∀x,y,l.x ∈ l → x ≠ y → x ∈ (remove_nat y l).
intros 3;elim l
  [elim (not_in_list_nil ? ? H);
  |simplify;elim (decidable_eq_nat y a)
     [rewrite > (eq_to_eqb_true ? ? H3);simplify;apply H
        [inversion H1;intros;destruct;
           [elim H2;reflexivity
           |assumption]
        |assumption]
     |rewrite > (not_eq_to_eqb_false ? ? H3);simplify;
      inversion H1;intros;destruct;autobatch]]
qed.

lemma swap_case: ∀u,v,x.(swap u v x) = u ∨ (swap u v x) = v ∨ (swap u v x = x).
intros;unfold in match swap;simplify;elim (eqb x u);simplify
  [autobatch
  |elim (eqb x v);simplify;autobatch]
qed.
    
definition distinct_list ≝
λl.∀n,m.n < length ? l → m < length ? l → n ≠ m → nth ? l O n ≠ nth ? l O m.

lemma posn_nth: ∀l,n.distinct_list l → n < length ? l → 
                    posn l (nth ? l O n) = n.
intro;elim l
  [simplify in H1;elim (not_le_Sn_O ? H1)
  |simplify in H2;generalize in match H2;elim n
     [simplify;rewrite > eqb_n_n;simplify;reflexivity
     |simplify;cut (nth ? (a::l1) O (S n1) ≠ nth ? (a::l1) O O)
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
           |(*** *:autobatch; *)
            apply H4
           |simplify;autobatch
           |intro;elim (not_eq_O_S n1);symmetry;assumption]]]]
qed.

lemma nth_in_list : ∀l,n. n < length ? l → (nth ? l O n) ∈ l.
intro;elim l
  [simplify in H;elim (not_le_Sn_O ? H)
  |generalize in match H1;elim n;simplify
     [apply in_list_head
     |apply in_list_cons;apply H;simplify in H3;apply (le_S_S_to_le ? ? H3)]]
qed.

lemma lookup_nth : \forall l,n.n < length ? l \to 
                   lookup (nth nat l O n) l = true.
intro;elim l
  [elim (not_le_Sn_O ? H);
  |generalize in match H1;elim n;simplify
     [rewrite > eqb_n_n;reflexivity
     |elim (eqb (nth nat l1 O n1) a);simplify;
        [reflexivity
        |apply H;apply le_S_S_to_le;assumption]]]
qed.
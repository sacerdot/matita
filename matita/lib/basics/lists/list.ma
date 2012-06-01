(*
    ||M||  This file is part of HELM, an Hypertextual, Electronic        
    ||A||  Library of Mathematics, developed at the Computer Science     
    ||T||  Department of the University of Bologna, Italy.                     
    ||I||                                                                 
    ||T||  
    ||A||  
    \   /  This file is distributed under the terms of the       
     \ /   GNU General Public License Version 2   
      V_______________________________________________________________ *)

include "basics/types.ma".
include "arithmetics/nat.ma".

inductive list (A:Type[0]) : Type[0] :=
  | nil: list A
  | cons: A -> list A -> list A.

notation "hvbox(hd break :: tl)"
  right associative with precedence 47
  for @{'cons $hd $tl}.

notation "[ list0 x sep ; ]"
  non associative with precedence 90
  for ${fold right @'nil rec acc @{'cons $x $acc}}.

notation "hvbox(l1 break @ l2)"
  right associative with precedence 47
  for @{'append $l1 $l2 }.

interpretation "nil" 'nil = (nil ?).
interpretation "cons" 'cons hd tl = (cons ? hd tl).

definition is_nil: ∀A:Type[0].list A → Prop ≝
 λA.λl.match l with [ nil ⇒ True | cons hd tl ⇒ False ].

theorem nil_cons:
  ∀A:Type[0].∀l:list A.∀a:A. a::l ≠ [].
  #A #l #a @nmk #Heq (change with (is_nil ? (a::l))) >Heq //
qed.

(*
let rec id_list A (l: list A) on l :=
  match l with
  [ nil => []
  | (cons hd tl) => hd :: id_list A tl ]. *)

let rec append A (l1: list A) l2 on l1 ≝ 
  match l1 with
  [ nil ⇒  l2
  | cons hd tl ⇒  hd :: append A tl l2 ].

definition hd ≝ λA.λl: list A.λd:A.
  match l with [ nil ⇒ d | cons a _ ⇒ a].

definition tail ≝  λA.λl: list A.
  match l with [ nil ⇒  [] | cons hd tl ⇒  tl].
  
definition option_hd ≝ 
  λA.λl:list A. match l with
  [ nil ⇒ None ?
  | cons a _ ⇒ Some ? a ].

interpretation "append" 'append l1 l2 = (append ? l1 l2).

theorem append_nil: ∀A.∀l:list A.l @ [] = l.
#A #l (elim l) normalize // qed.

theorem associative_append: 
 ∀A.associative (list A) (append A).
#A #l1 #l2 #l3 (elim l1) normalize // qed.

theorem append_cons:∀A.∀a:A.∀l,l1.l@(a::l1)=(l@[a])@l1.
#A #a #l #l1 >associative_append // qed.

theorem nil_append_elim: ∀A.∀l1,l2: list A.∀P:?→?→Prop. 
  l1@l2=[] → P (nil A) (nil A) → P l1 l2.
#A #l1 #l2 #P (cases l1) normalize //
#a #l3 #heq destruct
qed.

theorem nil_to_nil:  ∀A.∀l1,l2:list A.
  l1@l2 = [] → l1 = [] ∧ l2 = [].
#A #l1 #l2 #isnil @(nil_append_elim A l1 l2) /2/
qed.

lemma cons_injective_l : ∀A.∀a1,a2:A.∀l1,l2.a1::l1 = a2::l2 → a1 = a2.
#A #a1 #a2 #l1 #l2 #Heq destruct //
qed.

lemma cons_injective_r : ∀A.∀a1,a2:A.∀l1,l2.a1::l1 = a2::l2 → l1 = l2.
#A #a1 #a2 #l1 #l2 #Heq destruct //
qed.

(**************************** iterators ******************************)

let rec map (A,B:Type[0]) (f: A → B) (l:list A) on l: list B ≝
 match l with [ nil ⇒ nil ? | cons x tl ⇒ f x :: (map A B f tl)].

lemma map_append : ∀A,B,f,l1,l2.
  (map A B f l1) @ (map A B f l2) = map A B f (l1@l2).
#A #B #f #l1 elim l1
[ #l2 @refl
| #h #t #IH #l2 normalize //
] qed.
  
let rec foldr (A,B:Type[0]) (f:A → B → B) (b:B) (l:list A) on l :B ≝  
 match l with [ nil ⇒ b | cons a l ⇒ f a (foldr A B f b l)].
 
definition filter ≝ 
  λT.λp:T → bool.
  foldr T (list T) (λx,l0.if p x then x::l0 else l0) (nil T).

(* compose f [a1;...;an] [b1;...;bm] = 
  [f a1 b1; ... ;f an b1; ... ;f a1 bm; f an bm] *)
 
definition compose ≝ λA,B,C.λf:A→B→C.λl1,l2.
    foldr ?? (λi,acc.(map ?? (f i) l2)@acc) [ ] l1.

lemma filter_true : ∀A,l,a,p. p a = true → 
  filter A p (a::l) = a :: filter A p l.
#A #l #a #p #pa (elim l) normalize >pa normalize // qed.

lemma filter_false : ∀A,l,a,p. p a = false → 
  filter A p (a::l) = filter A p l.
#A #l #a #p #pa (elim l) normalize >pa normalize // qed.

theorem eq_map : ∀A,B,f,g,l. (∀x.f x = g x) → map A B f l = map A B g l.
#A #B #f #g #l #eqfg (elim l) normalize // qed.

(**************************** reverse *****************************)
let rec rev_append S (l1,l2:list S) on l1 ≝
  match l1 with 
  [ nil ⇒ l2
  | cons a tl ⇒ rev_append S tl (a::l2)
  ]
.

definition reverse ≝λS.λl.rev_append S l [].

lemma reverse_single : ∀S,a. reverse S [a] = [a]. 
// qed.

lemma rev_append_def : ∀S,l1,l2. 
  rev_append S l1 l2 = (reverse S l1) @ l2 .
#S #l1 elim l1 normalize // 
qed.

lemma reverse_cons : ∀S,a,l. reverse S (a::l) = (reverse S l)@[a].
#S #a #l whd in ⊢ (??%?); // 
qed.

lemma reverse_append: ∀S,l1,l2. 
  reverse S (l1 @ l2) = (reverse S l2)@(reverse S l1).
#S #l1 elim l1 [normalize // | #a #tl #Hind #l2 >reverse_cons
>reverse_cons // qed.

lemma reverse_reverse : ∀S,l. reverse S (reverse S l) = l.
#S #l elim l // #a #tl #Hind >reverse_cons >reverse_append 
normalize // qed.

(* an elimination principle for lists working on the tail;
useful for strings *)
lemma list_elim_left: ∀S.∀P:list S → Prop. P (nil S) →
(∀a.∀tl.P tl → P (tl@[a])) → ∀l. P l.
#S #P #Pnil #Pstep #l <(reverse_reverse … l) 
generalize in match (reverse S l); #l elim l //
#a #tl #H >reverse_cons @Pstep //
qed.

(**************************** length ******************************)

let rec length (A:Type[0]) (l:list A) on l ≝ 
  match l with 
    [ nil ⇒ 0
    | cons a tl ⇒ S (length A tl)].

notation "|M|" non associative with precedence 65 for @{'norm $M}.
interpretation "norm" 'norm l = (length ? l).

lemma length_tail: ∀A,l. length ? (tail A l) = pred (length ? l).
#A #l elim l // 
qed.

lemma length_append: ∀A.∀l1,l2:list A. 
  |l1@l2| = |l1|+|l2|.
#A #l1 elim l1 // normalize /2/
qed.

lemma length_map: ∀A,B,l.∀f:A→B. length ? (map ?? f l) = length ? l.
#A #B #l #f elim l // #a #tl #Hind normalize //
qed.

lemma length_reverse: ∀A.∀l:list A. 
  |reverse A l| = |l|.
#A #l elim l // #a #l0 #IH >reverse_cons >length_append normalize //
qed.

(****************** traversing two lists in parallel *****************)
lemma list_ind2 : 
  ∀T1,T2:Type[0].∀l1:list T1.∀l2:list T2.∀P:list T1 → list T2 → Prop.
  length ? l1 = length ? l2 →
  (P [] []) → 
  (∀tl1,tl2,hd1,hd2. P tl1 tl2 → P (hd1::tl1) (hd2::tl2)) → 
  P l1 l2.
#T1 #T2 #l1 #l2 #P #Hl #Pnil #Pcons
generalize in match Hl; generalize in match l2;
elim l1
[#l2 cases l2 // normalize #t2 #tl2 #H destruct
|#t1 #tl1 #IH #l2 cases l2
   [normalize #H destruct
   |#t2 #tl2 #H @Pcons @IH normalize in H; destruct // ]
]
qed.

lemma list_cases2 : 
  ∀T1,T2:Type[0].∀l1:list T1.∀l2:list T2.∀P:Prop.
  length ? l1 = length ? l2 →
  (l1 = [] → l2 = [] → P) → 
  (∀hd1,hd2,tl1,tl2.l1 = hd1::tl1 → l2 = hd2::tl2 → P) → P.
#T1 #T2 #l1 #l2 #P #Hl @(list_ind2 … Hl)
[ #Pnil #Pcons @Pnil //
| #tl1 #tl2 #hd1 #hd2 #IH1 #IH2 #Hp @Hp // ]
qed.

(*********************** properties of append ***********************)
lemma append_l1_injective : 
  ∀A.∀l1,l2,l3,l4:list A. |l1| = |l2| → l1@l3 = l2@l4 → l1 = l2.
#a #l1 #l2 #l3 #l4 #Hlen @(list_ind2 … Hlen) //
#tl1 #tl2 #hd1 #hd2 #IH normalize #Heq destruct @eq_f /2/
qed.
  
lemma append_l2_injective : 
  ∀A.∀l1,l2,l3,l4:list A. |l1| = |l2| → l1@l3 = l2@l4 → l3 = l4.
#a #l1 #l2 #l3 #l4 #Hlen @(list_ind2 … Hlen) normalize //
#tl1 #tl2 #hd1 #hd2 #IH normalize #Heq destruct /2/
qed.

lemma append_l1_injective_r :
  ∀A.∀l1,l2,l3,l4:list A. |l3| = |l4| → l1@l3 = l2@l4 → l1 = l2.
#a #l1 #l2 #l3 #l4 #Hlen #Heq lapply (eq_f … (reverse ?) … Heq)
>reverse_append >reverse_append #Heq1
lapply (append_l2_injective … Heq1) [ // ] #Heq2
lapply (eq_f … (reverse ?) … Heq2) //
qed.
  
lemma append_l2_injective_r : 
  ∀A.∀l1,l2,l3,l4:list A. |l3| = |l4| → l1@l3 = l2@l4 → l3 = l4.
#a #l1 #l2 #l3 #l4 #Hlen #Heq lapply (eq_f … (reverse ?) … Heq)
>reverse_append >reverse_append #Heq1
lapply (append_l1_injective … Heq1) [ // ] #Heq2
lapply (eq_f … (reverse ?) … Heq2) //
qed.

lemma length_rev_append: ∀A.∀l,acc:list A. 
  |rev_append ? l acc| = |l|+|acc|.
#A #l elim l // #a #tl #Hind normalize 
#acc >Hind normalize // 
qed.

(****************************** mem ********************************)
let rec mem A (a:A) (l:list A) on l ≝
  match l with
  [ nil ⇒ False
  | cons hd tl ⇒ a=hd ∨ mem A a tl
  ]. 

(***************************** split *******************************)
let rec split_rev A (l:list A) acc n on n ≝ 
  match n with 
  [O ⇒ 〈acc,l〉
  |S m ⇒ match l with 
    [nil ⇒ 〈acc,[]〉
    |cons a tl ⇒ split_rev A tl (a::acc) m
    ]
  ].
  
definition split ≝ λA,l,n.
  let 〈l1,l2〉 ≝ split_rev A l [] n in 〈reverse ? l1,l2〉.

lemma split_rev_len: ∀A,n,l,acc. n ≤ |l| →
  |\fst (split_rev A l acc n)| = n+|acc|.
#A #n elim n // #m #Hind *
  [normalize #acc #Hfalse @False_ind /2/
  |#a #tl #acc #Hlen normalize >Hind 
    [normalize // |@le_S_S_to_le //]
  ]
qed.

lemma split_len: ∀A,n,l. n ≤ |l| →
  |\fst (split A l n)| = n.
#A #n #l #Hlen normalize >(eq_pair_fst_snd ?? (split_rev …))
normalize >length_reverse  >(split_rev_len … [ ] Hlen) normalize //
qed.
  
lemma split_rev_eq: ∀A,n,l,acc. n ≤ |l| → 
  reverse ? acc@ l = 
    reverse ? (\fst (split_rev A l acc n))@(\snd (split_rev A l acc n)).
 #A #n elim n //
 #m #Hind * 
   [#acc whd in ⊢ ((??%)→?); #False_ind /2/ 
   |#a #tl #acc #Hlen >append_cons <reverse_single <reverse_append 
    @(Hind tl) @le_S_S_to_le @Hlen
   ]
qed.
 
lemma split_eq: ∀A,n,l. n ≤ |l| → 
  l = (\fst (split A l n))@(\snd (split A l n)).
#A #n #l #Hlen change with ((reverse ? [ ])@l) in ⊢ (??%?);
>(split_rev_eq … Hlen) normalize 
>(eq_pair_fst_snd ?? (split_rev A l [] n)) %
qed.

lemma split_exists: ∀A,n.∀l:list A. n ≤ |l| → 
  ∃l1,l2. l = l1@l2 ∧ |l1| = n.
#A #n #l #Hlen @(ex_intro … (\fst (split A l n)))
@(ex_intro … (\snd (split A l n))) % /2/
qed.
  
(****************************** nth ********************************)
let rec nth n (A:Type[0]) (l:list A) (d:A)  ≝  
  match n with
    [O ⇒ hd A l d
    |S m ⇒ nth m A (tail A l) d].

lemma nth_nil: ∀A,a,i. nth i A ([]) a = a.
#A #a #i elim i normalize //
qed.

(****************************** nth_opt ********************************)
let rec nth_opt (A:Type[0]) (n:nat) (l:list A) on l : option A ≝
match l with
[ nil ⇒ None ?
| cons h t ⇒ match n with [ O ⇒ Some ? h | S m ⇒ nth_opt A m t ]
].

(**************************** All *******************************)

let rec All (A:Type[0]) (P:A → Prop) (l:list A) on l : Prop ≝
match l with
[ nil ⇒ True
| cons h t ⇒ P h ∧ All A P t
].

lemma All_mp : ∀A,P,Q. (∀a.P a → Q a) → ∀l. All A P l → All A Q l.
#A #P #Q #H #l elim l normalize //
#h #t #IH * /3/
qed.

lemma All_nth : ∀A,P,n,l.
  All A P l →
  ∀a.
  nth_opt A n l = Some A a →
  P a.
#A #P #n elim n
[ * [ #_ #a #E whd in E:(??%?); destruct
    | #hd #tl * #H #_ #a #E whd in E:(??%?); destruct @H
    ]
| #m #IH *
  [ #_ #a #E whd in E:(??%?); destruct
  | #hd #tl * #_ whd in ⊢ (? → ∀_.??%? → ?); @IH
  ]
] qed.

(**************************** Exists *******************************)

let rec Exists (A:Type[0]) (P:A → Prop) (l:list A) on l : Prop ≝
match l with
[ nil ⇒ False
| cons h t ⇒ (P h) ∨ (Exists A P t)
].

lemma Exists_append : ∀A,P,l1,l2.
  Exists A P (l1 @ l2) → Exists A P l1 ∨ Exists A P l2.
#A #P #l1 elim l1
[ normalize /2/
| #h #t #IH #l2 *
  [ #H /3/
  | #H cases (IH l2 H) /3/
  ]
] qed.

lemma Exists_append_l : ∀A,P,l1,l2.
  Exists A P l1 → Exists A P (l1@l2).
#A #P #l1 #l2 elim l1
[ *
| #h #t #IH *
  [ #H %1 @H
  | #H %2 @IH @H
  ]
] qed.

lemma Exists_append_r : ∀A,P,l1,l2.
  Exists A P l2 → Exists A P (l1@l2).
#A #P #l1 #l2 elim l1
[ #H @H
| #h #t #IH #H %2 @IH @H
] qed.

lemma Exists_add : ∀A,P,l1,x,l2. Exists A P (l1@l2) → Exists A P (l1@x::l2).
#A #P #l1 #x #l2 elim l1
[ normalize #H %2 @H
| #h #t #IH normalize * [ #H %1 @H | #H %2 @IH @H ]
qed.

lemma Exists_mid : ∀A,P,l1,x,l2. P x → Exists A P (l1@x::l2).
#A #P #l1 #x #l2 #H elim l1
[ %1 @H
| #h #t #IH %2 @IH
] qed.

lemma Exists_map : ∀A,B,P,Q,f,l.
Exists A P l →
(∀a.P a → Q (f a)) →
Exists B Q (map A B f l).
#A #B #P #Q #f #l elim l //
#h #t #IH * [ #H #F %1 @F @H | #H #F %2 @IH [ @H | @F ] ] qed.

lemma Exists_All : ∀A,P,Q,l.
  Exists A P l →
  All A Q l →
  ∃x. P x ∧ Q x.
#A #P #Q #l elim l [ * | #hd #tl #IH * [ #H1 * #H2 #_ %{hd} /2/ | #H1 * #_ #H2 @IH // ]
qed.

(**************************** fold *******************************)

let rec fold (A,B:Type[0]) (op:B → B → B) (b:B) (p:A→bool) (f:A→B) (l:list A) on l :B ≝  
 match l with 
  [ nil ⇒ b 
  | cons a l ⇒
     if p a then op (f a) (fold A B op b p f l)
     else fold A B op b p f l].
      
notation "\fold  [ op , nil ]_{ ident i ∈ l | p} f"
  with precedence 80
for @{'fold $op $nil (λ${ident i}. $p) (λ${ident i}. $f) $l}.

notation "\fold [ op , nil ]_{ident i ∈ l } f"
  with precedence 80
for @{'fold $op $nil (λ${ident i}.true) (λ${ident i}. $f) $l}.

interpretation "\fold" 'fold op nil p f l = (fold ? ? op nil p f l).

theorem fold_true: 
∀A,B.∀a:A.∀l.∀p.∀op:B→B→B.∀nil.∀f:A→B. p a = true → 
  \fold[op,nil]_{i ∈ a::l| p i} (f i) = 
    op (f a) \fold[op,nil]_{i ∈ l| p i} (f i). 
#A #B #a #l #p #op #nil #f #pa normalize >pa // qed.

theorem fold_false: 
∀A,B.∀a:A.∀l.∀p.∀op:B→B→B.∀nil.∀f.
p a = false → \fold[op,nil]_{i ∈ a::l| p i} (f i) = 
  \fold[op,nil]_{i ∈ l| p i} (f i).
#A #B #a #l #p #op #nil #f #pa normalize >pa // qed.

theorem fold_filter: 
∀A,B.∀a:A.∀l.∀p.∀op:B→B→B.∀nil.∀f:A →B.
  \fold[op,nil]_{i ∈ l| p i} (f i) = 
    \fold[op,nil]_{i ∈ (filter A p l)} (f i).
#A #B #a #l #p #op #nil #f elim l //  
#a #tl #Hind cases(true_or_false (p a)) #pa 
  [ >filter_true // > fold_true // >fold_true //
  | >filter_false // >fold_false // ]
qed.

record Aop (A:Type[0]) (nil:A) : Type[0] ≝
  {op :2> A → A → A; 
   nill:∀a. op nil a = a; 
   nilr:∀a. op a nil = a;
   assoc: ∀a,b,c.op a (op b c) = op (op a b) c
  }.

theorem fold_sum: ∀A,B. ∀I,J:list A.∀nil.∀op:Aop B nil.∀f.
  op (\fold[op,nil]_{i∈I} (f i)) (\fold[op,nil]_{i∈J} (f i)) =
    \fold[op,nil]_{i∈(I@J)} (f i).
#A #B #I #J #nil #op #f (elim I) normalize 
  [>nill //|#a #tl #Hind <assoc //]
qed.

(********************** lhd and ltl ******************************)

let rec lhd (A:Type[0]) (l:list A) n on n ≝ match n with
   [ O   ⇒ nil …
   | S n ⇒ match l with [ nil ⇒ nil … | cons a l ⇒ a :: lhd A l n ]
   ].

let rec ltl (A:Type[0]) (l:list A) n on n ≝ match n with
   [ O   ⇒ l
   | S n ⇒ ltl A (tail … l) n
   ].

lemma lhd_nil: ∀A,n. lhd A ([]) n = [].
#A #n elim n //
qed.

lemma ltl_nil: ∀A,n. ltl A ([]) n = [].
#A #n elim n normalize //
qed.

lemma lhd_cons_ltl: ∀A,n,l. lhd A l n @ ltl A l n = l.
#A #n elim n -n //
#n #IHn #l elim l normalize //
qed.

lemma length_ltl: ∀A,n,l. |ltl A l n| = |l| - n.
#A #n elim n -n // 
#n #IHn *; normalize /2/
qed.

(********************** find ******************************)
let rec find (A,B:Type[0]) (f:A → option B) (l:list A) on l : option B ≝
match l with
[ nil ⇒ None B
| cons h t ⇒
    match f h with
    [ None ⇒ find A B f t
    | Some b ⇒ Some B b
    ]
].

(********************** position_of ******************************)
let rec position_of_aux (A:Type[0]) (found: A → bool) (l:list A) (acc:nat) on l : option nat ≝
match l with
[ nil ⇒ None ?
| cons h t ⇒
   match found h with [true ⇒ Some … acc | false ⇒ position_of_aux … found t (S acc)]].

definition position_of: ∀A:Type[0]. (A → bool) → list A → option nat ≝
 λA,found,l. position_of_aux A found l 0.


(********************** make_list ******************************)
let rec make_list (A:Type[0]) (a:A) (n:nat) on n : list A ≝
match n with
[ O ⇒ [ ]
| S m ⇒ a::(make_list A a m)
].

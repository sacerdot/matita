include "basics/types.ma".
include "basics/nat.ma".

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

definition not_nil: ∀A:Type[0].list A → Prop ≝
 λA.λl.match l with [ nil ⇒ True | cons hd tl ⇒ False ].

theorem nil_cons:
  ∀A:Type[0].∀l:list A.∀a:A. a::l ≠ [].
  #A #l #a @nmk #Heq (change with (not_nil ? (a::l))) >Heq //
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
    [ nil ⇒ O
    | cons a tl ⇒ S (length A tl)].

notation "|M|" non associative with precedence 65 for @{'norm $M}.
interpretation "norm" 'norm l = (length ? l).

lemma length_append: ∀A.∀l1,l2:list A. 
  |l1@l2| = |l1|+|l2|.
#A #l1 elim l1 // normalize /2/
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


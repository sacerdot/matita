(* boolean functions over lists *)

include "basics/list.ma".
include "basics/sets.ma".
include "basics/deqsets.ma".

(********* search *********)

let rec memb (S:DeqSet) (x:S) (l: list S) on l  ≝
  match l with
  [ nil ⇒ false
  | cons a tl ⇒ (x == a) ∨ memb S x tl
  ].

notation < "\memb x l" non associative with precedence 90 for @{'memb $x $l}.
interpretation "boolean membership" 'memb a l = (memb ? a l).

lemma memb_hd: ∀S,a,l. memb S a (a::l) = true.
#S #a #l normalize >(proj2 … (eqb_true S …) (refl S a)) //
qed.

lemma memb_cons: ∀S,a,b,l. 
  memb S a l = true → memb S a (b::l) = true.
#S #a #b #l normalize cases (a==b) normalize // 
qed.

lemma memb_single: ∀S,a,x. memb S a [x] = true → a = x.
#S #a #x normalize cases (true_or_false … (a==x)) #H
  [#_ >(\P H) // |>H normalize #abs @False_ind /2/]
qed.

lemma memb_append: ∀S,a,l1,l2. 
memb S a (l1@l2) = true →
  memb S a l1= true ∨ memb S a l2 = true.
#S #a #l1 elim l1 normalize [#l2 #H %2 //] 
#b #tl #Hind #l2 cases (a==b) normalize /2/ 
qed. 

lemma memb_append_l1: ∀S,a,l1,l2. 
 memb S a l1= true → memb S a (l1@l2) = true.
#S #a #l1 elim l1 normalize
  [normalize #le #abs @False_ind /2/
  |#b #tl #Hind #l2 cases (a==b) normalize /2/ 
  ]
qed. 

lemma memb_append_l2: ∀S,a,l1,l2. 
 memb S a l2= true → memb S a (l1@l2) = true.
#S #a #l1 elim l1 normalize //
#b #tl #Hind #l2 cases (a==b) normalize /2/ 
qed. 

lemma memb_exists: ∀S,a,l.memb S a l = true → 
  ∃l1,l2.l=l1@(a::l2).
#S #a #l elim l [normalize #abs @False_ind /2/]
#b #tl #Hind #H cases (orb_true_l … H)
  [#eqba @(ex_intro … (nil S)) @(ex_intro … tl) >(\P eqba) //
  |#mem_tl cases (Hind mem_tl) #l1 * #l2 #eqtl
   @(ex_intro … (b::l1)) @(ex_intro … l2) >eqtl //
  ]
qed.

lemma not_memb_to_not_eq: ∀S,a,b,l. 
 memb S a l = false → memb S b l = true → a==b = false.
#S #a #b #l cases (true_or_false (a==b)) // 
#eqab >(\P eqab) #H >H #abs @False_ind /2/
qed. 
 
lemma memb_map: ∀S1,S2,f,a,l. memb S1 a l= true → 
  memb S2 (f a) (map … f l) = true.
#S1 #S2 #f #a #l elim l normalize [//]
#x #tl #memba cases (true_or_false (a==x))
  [#eqx >eqx >(\P eqx) >(\b (refl … (f x))) normalize //
  |#eqx >eqx cases (f a==f x) normalize /2/
  ]
qed.

lemma memb_compose: ∀S1,S2,S3,op,a1,a2,l1,l2.   
  memb S1 a1 l1 = true → memb S2 a2 l2 = true →
  memb S3 (op a1 a2) (compose S1 S2 S3 op l1 l2) = true.
#S1 #S2 #S3 #op #a1 #a2 #l1 elim l1 [normalize //]
#x #tl #Hind #l2 #memba1 #memba2 cases (orb_true_l … memba1)
  [#eqa1 >(\P eqa1) @memb_append_l1 @memb_map // 
  |#membtl @memb_append_l2 @Hind //
  ]
qed.

(**************** unicity test *****************)

let rec uniqueb (S:DeqSet) l on l : bool ≝
  match l with 
  [ nil ⇒ true
  | cons a tl ⇒ notb (memb S a tl) ∧ uniqueb S tl
  ].

(* unique_append l1 l2 add l1 in fornt of l2, but preserving unicity *)

let rec unique_append (S:DeqSet) (l1,l2: list S) on l1 ≝
  match l1 with
  [ nil ⇒ l2
  | cons a tl ⇒ 
     let r ≝ unique_append S tl l2 in
     if memb S a r then r else a::r
  ].

axiom unique_append_elim: ∀S:DeqSet.∀P: S → Prop.∀l1,l2. 
(∀x. memb S x l1 = true → P x) → (∀x. memb S x l2 = true → P x) →
∀x. memb S x (unique_append S l1 l2) = true → P x. 

lemma unique_append_unique: ∀S,l1,l2. uniqueb S l2 = true →
  uniqueb S (unique_append S l1 l2) = true.
#S #l1 elim l1 normalize // #a #tl #Hind #l2 #uniquel2
cases (true_or_false … (memb S a (unique_append S tl l2))) 
#H >H normalize [@Hind //] >H normalize @Hind //
qed.

(******************* sublist *******************)
definition sublist ≝ 
  λS,l1,l2.∀a. memb S a l1 = true → memb S a l2 = true.

lemma sublist_length: ∀S,l1,l2. 
 uniqueb S l1 = true → sublist S l1 l2 → |l1| ≤ |l2|.
#S #l1 elim l1 // 
#a #tl #Hind #l2 #unique #sub
cut (∃l3,l4.l2=l3@(a::l4)) [@memb_exists @sub //]
* #l3 * #l4 #eql2 >eql2 >length_append normalize 
applyS le_S_S <length_append @Hind [@(andb_true_r … unique)]
>eql2 in sub; #sub #x #membx 
cases (memb_append … (sub x (orb_true_r2 … membx)))
  [#membxl3 @memb_append_l1 //
  |#membxal4 cases (orb_true_l … membxal4)
    [#eqxa @False_ind lapply (andb_true_l … unique)
     <(\P eqxa) >membx normalize /2/ |#membxl4 @memb_append_l2 //
    ]
  ]
qed.

lemma sublist_unique_append_l1: 
  ∀S,l1,l2. sublist S l1 (unique_append S l1 l2).
#S #l1 elim l1 normalize [#l2 #S #abs @False_ind /2/]
#x #tl #Hind #l2 #a 
normalize cases (true_or_false … (a==x)) #eqax >eqax 
[<(\P eqax) cases (true_or_false (memb S a (unique_append S tl l2)))
  [#H >H normalize // | #H >H normalize >(\b (refl … a)) //]
|cases (memb S x (unique_append S tl l2)) normalize 
  [/2/ |>eqax normalize /2/]
]
qed.

lemma sublist_unique_append_l2: 
  ∀S,l1,l2. sublist S l2 (unique_append S l1 l2).
#S #l1 elim l1 [normalize //] #x #tl #Hind normalize 
#l2 #a cases (memb S x (unique_append S tl l2)) normalize
[@Hind | cases (a==x) normalize // @Hind]
qed.

lemma decidable_sublist:∀S,l1,l2. 
  (sublist S l1 l2) ∨ ¬(sublist S l1 l2).
#S #l1 #l2 elim l1 
  [%1 #a normalize in ⊢ (%→?); #abs @False_ind /2/
  |#a #tl * #subtl 
    [cases (true_or_false (memb S a l2)) #memba
      [%1 whd #x #membx cases (orb_true_l … membx)
        [#eqax >(\P eqax) // |@subtl]
      |%2 @(not_to_not … (eqnot_to_noteq … true memba)) #H1 @H1 @memb_hd
      ]
    |%2 @(not_to_not … subtl) #H1 #x #H2 @H1 @memb_cons //
    ] 
  ]
qed.

(********************* filtering *****************)

lemma filter_true: ∀S,f,a,l. 
  memb S a (filter S f l) = true → f a = true.
#S #f #a #l elim l [normalize #H @False_ind /2/]
#b #tl #Hind cases (true_or_false (f b)) #H
normalize >H normalize [2:@Hind]
cases (true_or_false (a==b)) #eqab
  [#_ >(\P eqab) // | >eqab normalize @Hind]
qed. 
  
lemma memb_filter_memb: ∀S,f,a,l. 
  memb S a (filter S f l) = true → memb S a l = true.
#S #f #a #l elim l [normalize //]
#b #tl #Hind normalize (cases (f b)) normalize 
cases (a==b) normalize // @Hind
qed.
  
lemma memb_filter: ∀S,f,l,x. memb S x (filter ? f l) = true → 
memb S x l = true ∧ (f x = true).
/3/ qed.

lemma memb_filter_l: ∀S,f,x,l. (f x = true) → memb S x l = true →
memb S x (filter ? f l) = true.
#S #f #x #l #fx elim l normalize //
#b #tl #Hind cases (true_or_false (x==b)) #eqxb
  [<(\P eqxb) >(\b (refl … x)) >fx normalize >(\b (refl … x)) normalize //
  |>eqxb cases (f b) normalize [>eqxb normalize @Hind| @Hind]
  ]
qed. 

(********************* exists *****************)

let rec exists (A:Type[0]) (p:A → bool) (l:list A) on l : bool ≝
match l with
[ nil ⇒ false
| cons h t ⇒ orb (p h) (exists A p t)
].

lemma Exists_exists : ∀A,P,l.
  Exists A P l →
  ∃x. P x.
#A #P #l elim l [ * | #hd #tl #IH * [ #H %{hd} @H | @IH ]
qed.

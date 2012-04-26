include "basics/list.ma".
include "basics/sets.ma".
include "basics/deqsets.ma".

definition word ≝ λS:DeqSet.list S.

notation "ϵ" non associative with precedence 90 for @{ 'epsilon }.
interpretation "epsilon" 'epsilon = (nil ?).

(* concatenation *)
definition cat : ∀S,l1,l2,w.Prop ≝ 
  λS.λl1,l2.λw:word S.∃w1,w2.w1 @ w2 = w ∧ l1 w1 ∧ l2 w2.
notation "a · b" non associative with precedence 65 for @{ 'middot $a $b}.
interpretation "cat lang" 'middot a b = (cat ? a b).

let rec flatten (S : DeqSet) (l : list (word S)) on l : word S ≝ 
match l with [ nil ⇒ [ ] | cons w tl ⇒ w @ flatten ? tl ].

let rec conjunct (S : DeqSet) (l : list (word S)) (r : word S → Prop) on l: Prop ≝
match l with [ nil ⇒ True | cons w tl ⇒ r w ∧ conjunct ? tl r ]. 

(* kleene's star *)
definition star ≝ λS.λl.λw:word S.∃lw.flatten ? lw = w ∧ conjunct ? lw l. 
notation "a ^ *" non associative with precedence 90 for @{ 'star $a}.
interpretation "star lang" 'star l = (star ? l).

lemma cat_ext_l: ∀S.∀A,B,C:word S →Prop. 
  A =1 C  → A · B =1 C · B.
#S #A #B #C #H #w % * #w1 * #w2 * * #eqw #inw1 #inw2
cases (H w1) /6/ 
qed.

lemma cat_ext_r: ∀S.∀A,B,C:word S →Prop. 
  B =1 C → A · B =1 A · C.
#S #A #B #C #H #w % * #w1 * #w2 * * #eqw #inw1 #inw2
cases (H w2) /6/ 
qed.
  
lemma cat_empty_l: ∀S.∀A:word S→Prop. ∅ · A =1 ∅.
#S #A #w % [|*] * #w1 * #w2 * * #_ *
qed.

lemma distr_cat_r: ∀S.∀A,B,C:word S →Prop.
  (A ∪ B) · C =1  A · C ∪ B · C. 
#S #A #B #C #w %
  [* #w1 * #w2 * * #eqw * /6/ |* * #w1 * #w2 * * /6/] 
qed.

(* derivative *)

definition deriv ≝ λS.λA:word S → Prop.λa,w. A (a::w).

lemma deriv_middot: ∀S,A,B,a. ¬ A ϵ → 
  deriv S (A·B) a =1 (deriv S A a) · B.
#S #A #B #a #noteps #w normalize %
  [* #w1 cases w1 
    [* #w2 * * #_ #Aeps @False_ind /2/
    |#b #w2 * #w3 * * whd in ⊢ ((??%?)→?); #H destruct
     #H #H1 @(ex_intro … w2) @(ex_intro … w3) % // % //
    ]
  |* #w1 * #w2 * * #H #H1 #H2 @(ex_intro … (a::w1))
   @(ex_intro … w2) % // % normalize //
  ]
qed. 

(* star properties *)
lemma espilon_in_star: ∀S.∀A:word S → Prop.
  A^* ϵ.
#S #A @(ex_intro … [ ]) normalize /2/
qed.

lemma cat_to_star:∀S.∀A:word S → Prop.
  ∀w1,w2. A w1 → A^* w2 → A^* (w1@w2).
#S #A #w1 #w2 #Aw * #l * #H #H1 @(ex_intro … (w1::l)) 
% normalize /2/
qed.

lemma fix_star: ∀S.∀A:word S → Prop. 
  A^* =1 A · A^* ∪ {ϵ}.
#S #A #w %
  [* #l generalize in match w; -w cases l [normalize #w * /2/]
   #w1 #tl #w * whd in ⊢ ((??%?)→?); #eqw whd in ⊢ (%→?); *
   #w1A #cw1 %1 @(ex_intro … w1) @(ex_intro … (flatten S tl))
   % /2/ whd @(ex_intro … tl) /2/
  |* [2: whd in ⊢ (%→?); #eqw <eqw //]
   * #w1 * #w2 * * #eqw <eqw @cat_to_star 
  ]
qed.

lemma star_fix_eps : ∀S.∀A:word S → Prop.
  A^* =1 (A - {ϵ}) · A^* ∪ {ϵ}.  
#S #A #w %
  [* #l elim l 
    [* whd in ⊢ ((??%?)→?); #eqw #_ %2 <eqw // 
    |* [#tl #Hind * #H * #_ #H2 @Hind % [@H | //]
       |#a #w1 #tl #Hind * whd in ⊢ ((??%?)→?); #H1 * #H2 #H3 %1 
        @(ex_intro … (a::w1)) @(ex_intro … (flatten S tl)) %
         [% [@H1 | normalize % /2/] |whd @(ex_intro … tl) /2/]
       ]
    ]
  |* [* #w1 * #w2 * * #eqw * #H1 #_ <eqw @cat_to_star //
     | whd in ⊢ (%→?); #H <H //
     ]
  ]
qed. 
     
lemma star_epsilon: ∀S:DeqSet.∀A:word S → Prop.
  A^* ∪ {ϵ} =1 A^*.
#S #A #w % /2/ * // 
qed.
  
lemma epsilon_cat_r: ∀S.∀A:word S →Prop.
   A · {ϵ} =1  A. 
#S #A #w %
  [* #w1 * #w2 * * #eqw #inw1 normalize #eqw2 <eqw //
  |#inA @(ex_intro … w) @(ex_intro … [ ]) /3/
  ]
qed.

lemma epsilon_cat_l: ∀S.∀A:word S →Prop.
   {ϵ} · A =1  A. 
#S #A #w %
  [* #w1 * #w2 * * #eqw normalize #eqw2 <eqw <eqw2 //
  |#inA @(ex_intro … ϵ) @(ex_intro … w) /3/
  ]
qed.

lemma distr_cat_r_eps: ∀S.∀A,C:word S →Prop.
  (A ∪ {ϵ}) · C =1  A · C ∪ C. 
#S #A #C @eqP_trans [|@distr_cat_r |@eqP_union_l @epsilon_cat_l]
qed.


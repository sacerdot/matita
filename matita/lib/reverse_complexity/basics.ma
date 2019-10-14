include "basics/types.ma".
include "arithmetics/nat.ma".

(********************************** pairing ***********************************)
axiom pair: nat → nat → nat.
axiom fst : nat → nat.
axiom snd : nat → nat.

interpretation "abstract pair" 'pair f g = (pair f g). 

axiom fst_pair: ∀a,b. fst 〈a,b〉 = a.
axiom snd_pair: ∀a,b. snd 〈a,b〉 = b.
axiom surj_pair: ∀x. ∃a,b. x = 〈a,b〉. 

axiom le_fst : ∀p. fst p ≤ p.
axiom le_snd : ∀p. snd p ≤ p.
axiom le_pair: ∀a,a1,b,b1. a ≤ a1 → b ≤ b1 → 〈a,b〉 ≤ 〈a1,b1〉.

lemma expand_pair: ∀x. x = 〈fst x, snd x〉. 
#x lapply (surj_pair x) * #a * #b #Hx >Hx >fst_pair >snd_pair //
qed.

(************************************* U **************************************)
axiom U: nat → nat →nat → option nat. 

axiom monotonic_U: ∀i,x,n,m,y.n ≤m →
  U i x n = Some ? y → U i x m = Some ? y.
  
lemma unique_U: ∀i,x,n,m,yn,ym.
  U i x n = Some ? yn → U i x m = Some ? ym → yn = ym.
#i #x #n #m #yn #ym #Hn #Hm cases (decidable_le n m)
  [#lenm lapply (monotonic_U … lenm Hn) >Hm #HS destruct (HS) //
  |#ltmn lapply (monotonic_U … n … Hm) [@lt_to_le @not_le_to_lt //]
   >Hn #HS destruct (HS) //
  ]
qed.

definition code_for ≝ λf,i.∀x.
  ∃n.∀m. n ≤ m → U i x m = f x.

definition terminate ≝ λi,x,r. ∃y. U i x r = Some ? y. 

notation "{i ⊙ x} ↓ r" with precedence 60 for @{terminate $i $x $r}. 

lemma terminate_dec: ∀i,x,n. {i ⊙ x} ↓ n ∨ ¬ {i ⊙ x} ↓ n.
#i #x #n normalize cases (U i x n)
  [%2 % * #y #H destruct|#y %1 %{y} //]
qed.
  
lemma monotonic_terminate: ∀i,x,n,m.
  n ≤ m → {i ⊙ x} ↓ n → {i ⊙ x} ↓ m.
#i #x #n #m #lenm * #z #H %{z} @(monotonic_U … H) //
qed.

definition termb ≝ λi,x,t. 
  match U i x t with [None ⇒ false |Some y ⇒ true].

lemma termb_true_to_term: ∀i,x,t. termb i x t = true → {i ⊙ x} ↓ t.
#i #x #t normalize cases (U i x t) normalize [#H destruct | #y #_ %{y} //]
qed.    

lemma term_to_termb_true: ∀i,x,t. {i ⊙ x} ↓ t → termb i x t = true.
#i #x #t * #y #H normalize >H // 
qed.    

definition out ≝ λi,x,r. 
  match U i x r with [ None ⇒ 0 | Some z ⇒ z]. 

definition bool_to_nat: bool → nat ≝ 
  λb. match b with [true ⇒ 1 | false ⇒ 0]. 
  
coercion bool_to_nat. 

definition pU : nat → nat → nat → nat ≝ λi,x,r.〈termb i x r,out i x r〉.

lemma pU_vs_U_Some : ∀i,x,r,y. pU i x r = 〈1,y〉 ↔ U i x r = Some ? y.
#i #x #r #y % normalize
  [cases (U i x r) normalize 
    [#H cut (0=1) [lapply (eq_f … fst … H) >fst_pair >fst_pair #H @H] 
     #H1 destruct
    |#a #H cut (a=y) [lapply (eq_f … snd … H) >snd_pair >snd_pair #H1 @H1] 
     #H1 //
    ]
  |#H >H //]
qed.
  
lemma pU_vs_U_None : ∀i,x,r. pU i x r = 〈0,0〉 ↔ U i x r = None ?.
#i #x #r % normalize
  [cases (U i x r) normalize //
   #a #H cut (1=0) [lapply (eq_f … fst … H) >fst_pair >fst_pair #H1 @H1] 
   #H1 destruct
  |#H >H //]
qed.

lemma fst_pU: ∀i,x,r. fst (pU i x r) = termb i x r.
#i #x #r normalize cases (U i x r) normalize >fst_pair //
qed.

lemma snd_pU: ∀i,x,r. snd (pU i x r) = out i x r.
#i #x #r normalize cases (U i x r) normalize >snd_pair //
qed.


definition total ≝ λf.λx:nat. Some nat (f x).



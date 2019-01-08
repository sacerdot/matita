include "basics/types.ma".
include "arithmetics/minimization.ma".
include "arithmetics/bigops.ma".
include "arithmetics/sigma_pi.ma".
include "arithmetics/bounded_quantifiers.ma".
include "reverse_complexity/big_O.ma".

(************************* notation for minimization **************************)
notation "μ_{ ident i < n } p" 
  with precedence 80 for @{min $n 0 (λ${ident i}.$p)}.

notation "μ_{ ident i ≤ n } p" 
  with precedence 80 for @{min (S $n) 0 (λ${ident i}.$p)}.
  
notation "μ_{ ident i ∈ [a,b[ } p"
  with precedence 80 for @{min ($b-$a) $a (λ${ident i}.$p)}.
  
notation "μ_{ ident i ∈ [a,b] } p"
  with precedence 80 for @{min (S $b-$a) $a (λ${ident i}.$p)}.
  
(************************************ MAX *************************************)
notation "Max_{ ident i < n | p } f"
  with precedence 80
for @{'bigop $n max 0 (λ${ident i}. $p) (λ${ident i}. $f)}.

notation "Max_{ ident i < n } f"
  with precedence 80
for @{'bigop $n max 0 (λ${ident i}.true) (λ${ident i}. $f)}.

notation "Max_{ ident j ∈ [a,b[ } f"
  with precedence 80
for @{'bigop ($b-$a) max 0 (λ${ident j}.((λ${ident j}.true) (${ident j}+$a)))
  (λ${ident j}.((λ${ident j}.$f)(${ident j}+$a)))}.
  
notation "Max_{ ident j ∈ [a,b[ | p } f"
  with precedence 80
for @{'bigop ($b-$a) max 0 (λ${ident j}.((λ${ident j}.$p) (${ident j}+$a)))
  (λ${ident j}.((λ${ident j}.$f)(${ident j}+$a)))}.

lemma Max_assoc: ∀a,b,c. max (max a b) c = max a (max b c).
#a #b #c normalize cases (true_or_false (leb a b)) #leab >leab normalize
  [cases (true_or_false (leb b c )) #lebc >lebc normalize
    [>(le_to_leb_true a c) // @(transitive_le ? b) @leb_true_to_le //
    |>leab //
    ]
  |cases (true_or_false (leb b c )) #lebc >lebc normalize //
   >leab normalize >(not_le_to_leb_false a c) // @lt_to_not_le 
   @(transitive_lt ? b) @not_le_to_lt @leb_false_to_not_le //
  ]
qed.

lemma Max0 : ∀n. max 0 n = n.
// qed.

lemma Max0r : ∀n. max n 0 = n.
#n >commutative_max //
qed.

definition MaxA ≝ 
  mk_Aop nat 0 max Max0 Max0r (λa,b,c.sym_eq … (Max_assoc a b c)). 

definition MaxAC ≝ mk_ACop nat 0 MaxA commutative_max.

lemma le_Max: ∀f,p,n,a. a < n → p a = true →
  f a ≤  Max_{i < n | p i}(f i).
#f #p #n #a #ltan #pa 
>(bigop_diff p ? 0 MaxAC f a n) // @(le_maxl … (le_n ?))
qed.

lemma le_MaxI: ∀f,p,n,m,a. m ≤ a → a < n → p a = true →
  f a ≤  Max_{i ∈ [m,n[ | p i}(f i).
#f #p #n #m #a #lema #ltan #pa 
>(bigop_diff ? ? 0 MaxAC (λi.f (i+m)) (a-m) (n-m)) 
  [<plus_minus_m_m // @(le_maxl … (le_n ?))
  |<plus_minus_m_m //
  |/2 by monotonic_lt_minus_l/
  ]
qed.

lemma Max_le: ∀f,p,n,b. 
  (∀a.a < n → p a = true → f a ≤ b) → Max_{i < n | p i}(f i) ≤ b.
#f #p #n elim n #b #H // 
#b0 #H1 cases (true_or_false (p b)) #Hb
  [>bigop_Strue [2:@Hb] @to_max [@H1 // | @H #a #ltab #pa @H1 // @le_S //]
  |>bigop_Sfalse [2:@Hb] @H #a #ltab #pa @H1 // @le_S //
  ]
qed.

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


(********************************* complexity *********************************)

(* We assume operations have a minimal structural complexity MSC. 
For instance, for time complexity, MSC is equal to the size of input.
For space complexity, MSC is typically 0, since we only measure the
space required in addition to dimension of the input. *)

axiom MSC : nat → nat.
axiom MSC_le: ∀n. MSC n ≤ n.
axiom monotonic_MSC: monotonic ? le MSC.
axiom MSC_pair: ∀a,b. MSC 〈a,b〉 ≤ MSC a + MSC b.

(* C s i means i is running in O(s) *)
 
definition C ≝ λs,i.∃c.∃a.∀x.a ≤ x → ∃y. 
  U i x (c*(s x)) = Some ? y.

(* C f s means f ∈ O(s) where MSC ∈O(s) *)
definition CF ≝ λs,f.O s MSC ∧ ∃i.code_for (total f) i ∧ C s i.
 
lemma ext_CF : ∀f,g,s. (∀n. f n = g n) → CF s f → CF s g.
#f #g #s #Hext * #HO  * #i * #Hcode #HC % // %{i} %
  [#x cases (Hcode x) #a #H %{a} whd in match (total ??); <Hext @H | //] 
qed.

lemma ext_CF1 : ∀f,g,s. (∀n. f n = g n) → CF s g → CF s f.
#f #g #s #Hext * #HO  * #i * #Hcode #HC % // %{i} %
  [#x cases (Hcode x) #a #H %{a} whd in match (total ??); >Hext @H | //] 
qed.

lemma monotonic_CF: ∀s1,s2,f.(∀x. s1 x ≤  s2 x) → CF s1 f → CF s2 f.
#s1 #s2 #f #H * #HO * #i * #Hcode #Hs1 % 
  [cases HO #c * #a -HO #HO %{c} %{a} #n #lean @(transitive_le … (HO n lean))
   @le_times // 
  |%{i} % [//] cases Hs1 #c * #a -Hs1 #Hs1 %{c} %{a} #n #lean 
   cases(Hs1 n lean) #y #Hy %{y} @(monotonic_U …Hy) @le_times // 
  ]
qed.

lemma O_to_CF: ∀s1,s2,f.O s2 s1 → CF s1 f → CF s2 f.
#s1 #s2 #f #H * #HO * #i * #Hcode #Hs1 % 
  [@(O_trans … H) //
  |%{i} % [//] cases Hs1 #c * #a -Hs1 #Hs1 
   cases H #c1 * #a1 #Ha1 %{(c*c1)} %{(a+a1)} #n #lean 
   cases(Hs1 n ?) [2:@(transitive_le … lean) //] #y #Hy %{y} @(monotonic_U …Hy)
   >associative_times @le_times // @Ha1 @(transitive_le … lean) //
  ]
qed.

lemma timesc_CF: ∀s,f,c.CF (λx.c*s x) f → CF s f.
#s #f #c @O_to_CF @O_times_c 
qed.

(********************************* composition ********************************)
axiom CF_comp: ∀f,g,sf,sg,sh. CF sg g → CF sf f → 
  O sh (λx. sg x + sf (g x)) → CF sh (f ∘ g).
  
lemma CF_comp_ext: ∀f,g,h,sh,sf,sg. CF sg g → CF sf f → 
  (∀x.f(g x) = h x) → O sh (λx. sg x + sf (g x)) → CF sh h.
#f #g #h #sh #sf #sg #Hg #Hf #Heq #H @(ext_CF (f ∘ g))
  [#n normalize @Heq | @(CF_comp … H) //]
qed.

(* primitve recursion *)

(* no arguments *)

let rec prim_rec0 (k:nat) (h:nat →nat) n on n ≝ 
  match n with 
  [ O ⇒ k
  | S a ⇒ h 〈a, prim_rec0 k h a〉].
  
lemma prim_rec0_S: ∀k,h,n.
  prim_rec0 k h (S n) = h 〈n, prim_rec0 k h n〉.
// qed.

let rec prim_rec0_compl (k,sk:nat) (h,sh:nat →nat) n on n ≝ 
  match n with 
  [ O ⇒ sk
  | S a ⇒ prim_rec0_compl k sk h sh a + sh (prim_rec0 k h a)].

axiom CF_prim_rec0_gen: ∀k,h,sk,sh,sh1,sf. CF sh h →
  O sh1 (λx.snd x + sh 〈fst x,prim_rec0 k h (fst x)〉) → 
  O sf (prim_rec0 sk sh1) →
   CF sf (prim_rec0 k h).

lemma CF_prim_rec0: ∀k,h,sk,sh,sf. CF sh h → 
  O sf (prim_rec0 sk (λx. snd x + sh 〈fst x,prim_rec0 k h (fst x)〉))
   → CF sf (prim_rec0 k h).
#k #h #sk #sh #sf #Hh #HO @(CF_prim_rec0_gen … Hh … HO) @O_refl
qed.

(* with argument(s) m *)
let rec prim_rec (k,h:nat →nat) n m on n ≝ 
  match n with 
  [ O ⇒ k m
  | S a ⇒ h 〈a,〈prim_rec k h a m, m〉〉].
  
lemma prim_rec_S: ∀k,h,n,m.
  prim_rec k h (S n) m = h 〈n,〈prim_rec k h n m, m〉〉.
// qed.

lemma prim_rec_le: ∀k1,k2,h1,h2. (∀x.k1 x ≤ k2 x) → 
(∀x,y.x ≤y → h1 x ≤ h2 y) →
  ∀x,m. prim_rec k1 h1 x m ≤ prim_rec k2 h2 x m.
#k1 #k2 #h1 #h2 #lek #leh #x #m elim x //
#n #Hind normalize @leh @le_pair // @le_pair //
qed.
 
definition unary_pr ≝ λk,h,x. prim_rec k h (fst x) (snd x).

lemma prim_rec_unary: ∀k,h,a,b. 
  prim_rec k h a b = unary_pr k h 〈a,b〉.
#k #h #a #b normalize >fst_pair >snd_pair //
qed.
  

let rec prim_rec_compl (k,h,sk,sh:nat →nat) n m on n ≝ 
  match n with 
  [ O ⇒ sk m
  | S a ⇒ prim_rec_compl k h sk sh a m + sh (prim_rec k h a m)].

axiom CF_prim_rec_gen: ∀k,h,sk,sh,sh1. CF sk k → CF sh h →  
  O sh1 (λx. fst (snd x) + sh 〈fst x,〈unary_pr k h 〈fst x,snd (snd x)〉,snd (snd x)〉〉) → 
   CF (unary_pr sk sh1) (unary_pr k h).

lemma CF_prim_rec: ∀k,h,sk,sh,sf. CF sk k → CF sh h → 
  O sf (unary_pr sk (λx. fst (snd x) + sh 〈fst x,〈unary_pr k h 〈fst x,snd (snd x)〉,snd (snd x)〉〉)) 
   → CF sf (unary_pr k h).
#k #h #sk #sh #sf #Hk #Hh #Osf @(O_to_CF … Osf) @(CF_prim_rec_gen … Hk Hh) @O_refl
qed.
  
(**************************** primitive operations*****************************)

definition id ≝ λx:nat.x.

axiom CF_id: CF MSC id.
axiom CF_const: ∀k.CF MSC (λx.k).
axiom CF_compS: ∀h,f. CF h f → CF h (S ∘ f).
axiom CF_comp_fst: ∀h,f. CF h f → CF h (fst ∘ f).
axiom CF_comp_snd: ∀h,f. CF h f → CF h (snd ∘ f). 
axiom CF_comp_pair: ∀h,f,g. CF h f → CF h g → CF h (λx. 〈f x,g x〉). 

lemma CF_fst: CF MSC fst.
@(ext_CF (fst ∘ id)) [#n //] @(CF_comp_fst … CF_id)
qed.

lemma CF_snd: CF MSC snd.
@(ext_CF (snd ∘ id)) [#n //] @(CF_comp_snd … CF_id)
qed. 

(************************************** eqb ***********************************)
  
axiom CF_eqb: ∀h,f,g.
  CF h f → CF h g → CF h (λx.eqb (f x) (g x)).

(*********************************** maximum **********************************) 

alias symbol "pair" (instance 13) = "abstract pair".
alias symbol "pair" (instance 12) = "abstract pair".
alias symbol "and" (instance 11) = "boolean and".
alias symbol "plus" (instance 8) = "natural plus".
alias symbol "pair" (instance 7) = "abstract pair".
alias symbol "plus" (instance 6) = "natural plus".
alias symbol "pair" (instance 5) = "abstract pair".
alias id "max" = "cic:/matita/arithmetics/nat/max#def:2".
alias symbol "minus" (instance 3) = "natural minus".
lemma max_gen: ∀a,b,p,f,x. a ≤b → 
  max_{i ∈[a,b[ | p 〈i,x〉 }(f 〈i,x〉) = max_{i < b | leb a i ∧ p 〈i,x〉 }(f 〈i,x〉).
#a #b #p #f #x @(bigop_I_gen ????? MaxA) 
qed.

lemma max_prim_rec_base: ∀a,b,p,f,x. a ≤b → 
  max_{i < b| p 〈i,x〉 }(f 〈i,x〉) = 
    prim_rec (λi.0) 
    (λi.if p 〈fst i,x〉 then max (f 〈fst i,snd (snd i)〉) (fst (snd i)) else fst (snd i)) b x.
#a #b #p #f #x #leab >max_gen // elim b 
  [normalize //
  |#i #Hind >prim_rec_S >fst_pair >snd_pair >snd_pair >fst_pair
   cases (true_or_false (p 〈i,x〉)) #Hcase >Hcase
    [<Hind >bigop_Strue // |<Hind >bigop_Sfalse // ]
  ]
qed.

lemma max_prim_rec: ∀a,b,p,f,x. a ≤b → 
  max_{i ∈[a,b[ | p 〈i,x〉 }(f 〈i,x〉) = 
    prim_rec (λi.0) 
    (λi.if leb a (fst i) ∧ p 〈fst i,x〉 then max (f 〈fst i,snd (snd i)〉) (fst (snd i)) else fst (snd i)) b x.
#a #b #p #f #x #leab >max_gen // elim b 
  [normalize //
  |#i #Hind >prim_rec_S >fst_pair >snd_pair >snd_pair >fst_pair
   cases (true_or_false (leb a i ∧ p 〈i,x〉)) #Hcase >Hcase
    [<Hind >bigop_Strue // |<Hind >bigop_Sfalse // ]
  ]
qed.

(* FG: aliases added by matita compiled with OCaml 4.0.5, bah ??? *)
alias symbol "pair" (instance 15) = "abstract pair".
alias symbol "minus" (instance 14) = "natural minus".
alias symbol "plus" (instance 11) = "natural plus".
alias symbol "pair" (instance 10) = "abstract pair".
alias symbol "plus" (instance 13) = "natural plus".
alias symbol "pair" (instance 12) = "abstract pair".
alias symbol "plus" (instance 8) = "natural plus".
alias symbol "pair" (instance 7) = "abstract pair".
alias symbol "plus" (instance 6) = "natural plus".
alias symbol "pair" (instance 5) = "abstract pair".
alias id "max" = "cic:/matita/arithmetics/nat/max#def:2".
alias symbol "minus" (instance 3) = "natural minus".
lemma max_prim_rec1: ∀a,b,p,f,x.
  max_{i ∈[a x,b x[ | p 〈i,x〉 }(f 〈i,x〉) = 
    prim_rec (λi.0) 
    (λi.if p 〈fst i +fst (snd (snd i)),snd (snd (snd i))〉 
        then max (f 〈fst i +fst (snd (snd i)),snd (snd (snd i))〉) (fst (snd i)) 
        else fst (snd i)) (b x-a x) 〈a x ,x〉.
#a #b #p #f #x elim (b x-a x) 
  [normalize //
  |#i #Hind >prim_rec_S
   >fst_pair >snd_pair >snd_pair >fst_pair >snd_pair >fst_pair
   cases (true_or_false (p 〈i+a x,x〉)) #Hcase >Hcase
    [<Hind >bigop_Strue // |<Hind >bigop_Sfalse // ]
  ]
qed.

lemma sum_prim_rec1: ∀a,b,p,f,x.
  ∑_{i ∈[a x,b x[ | p 〈i,x〉 }(f 〈i,x〉) = 
    prim_rec (λi.0) 
    (λi.if p 〈fst i +fst (snd (snd i)),snd (snd (snd i))〉 
        then plus (f 〈fst i +fst (snd (snd i)),snd (snd (snd i))〉) (fst (snd i)) 
        else fst (snd i)) (b x-a x) 〈a x ,x〉.
#a #b #p #f #x elim (b x-a x) 
  [normalize //
  |#i #Hind >prim_rec_S
   >fst_pair >snd_pair >snd_pair >fst_pair >snd_pair >fst_pair
   cases (true_or_false (p 〈i+a x,x〉)) #Hcase >Hcase
    [<Hind >bigop_Strue // |<Hind >bigop_Sfalse // ]
  ]
qed.

(* FG: aliases added by matita compiled with OCaml 4.0.5, bah ??? *)
alias symbol "pair" (instance 15) = "abstract pair".
alias symbol "minus" (instance 14) = "natural minus".
alias symbol "plus" (instance 11) = "natural plus".
alias symbol "pair" (instance 10) = "abstract pair".
alias symbol "plus" (instance 13) = "natural plus".
alias symbol "pair" (instance 12) = "abstract pair".
alias symbol "plus" (instance 8) = "natural plus".
alias symbol "pair" (instance 7) = "abstract pair".
alias symbol "pair" (instance 6) = "abstract pair".
alias symbol "plus" (instance 4) = "natural plus".
alias symbol "pair" (instance 3) = "abstract pair".
alias symbol "minus" (instance 2) = "natural minus".
lemma bigop_prim_rec: ∀a,b,c,p,f,x.
  bigop (b x-a x) (λi:ℕ.p 〈i+a x,x〉) ? (c 〈a x,x〉) plus (λi:ℕ.f 〈i+a x,x〉) = 
    prim_rec c 
    (λi.if p 〈fst i +fst (snd (snd i)),snd (snd (snd i))〉 
        then plus (f 〈fst i +fst (snd (snd i)),snd (snd (snd i))〉) (fst (snd i)) 
        else fst (snd i)) (b x-a x) 〈a x ,x〉.
#a #b #c #p #f #x normalize elim (b x-a x) 
  [normalize //
  |#i #Hind >prim_rec_S
   >fst_pair >snd_pair >snd_pair >fst_pair >snd_pair >fst_pair
   cases (true_or_false (p 〈i+a x,x〉)) #Hcase >Hcase
    [<Hind >bigop_Strue // |<Hind >bigop_Sfalse // ]
  ]
qed.

(* FG: aliases added by matita compiled with OCaml 4.0.5, bah ??? *)
alias symbol "pair" (instance 15) = "abstract pair".
alias symbol "minus" (instance 14) = "natural minus".
alias symbol "minus" (instance 11) = "natural minus".
alias symbol "pair" (instance 10) = "abstract pair".
alias symbol "minus" (instance 13) = "natural minus".
alias symbol "pair" (instance 12) = "abstract pair".
alias symbol "minus" (instance 8) = "natural minus".
alias symbol "pair" (instance 7) = "abstract pair".
alias symbol "pair" (instance 6) = "abstract pair".
alias symbol "minus" (instance 4) = "natural minus".
alias symbol "pair" (instance 3) = "abstract pair".
alias symbol "minus" (instance 2) = "natural minus".
lemma bigop_prim_rec_dec: ∀a,b,c,p,f,x.
  bigop (b x-a x) (λi:ℕ.p 〈b x -i,x〉) ? (c 〈b x,x〉) plus (λi:ℕ.f 〈b x-i,x〉) = 
    prim_rec c 
    (λi.if p 〈fst (snd (snd i)) - fst i,snd (snd (snd i))〉 
        then plus (f 〈fst (snd (snd i)) - fst i,snd (snd (snd i))〉) (fst (snd i)) 
        else fst (snd i)) (b x-a x) 〈b x ,x〉.
#a #b #c #p #f #x normalize elim (b x-a x) 
  [normalize //
  |#i #Hind >prim_rec_S
   >fst_pair >snd_pair >snd_pair >fst_pair >snd_pair >fst_pair
   cases (true_or_false (p 〈b x - i,x〉)) #Hcase >Hcase
    [<Hind >bigop_Strue // |<Hind >bigop_Sfalse // ]
  ]
qed.

lemma bigop_prim_rec_dec1: ∀a,b,c,p,f,x.
  bigop (S(b x)-a x) (λi:ℕ.p 〈b x - i,x〉) ? (c 〈b x,x〉) plus (λi:ℕ.f 〈b x- i,x〉) = 
    prim_rec c 
    (λi.if p 〈fst (snd (snd i)) - (fst i),snd (snd (snd i))〉 
        then plus (f 〈fst (snd (snd i)) - (fst i),snd (snd (snd i))〉) (fst (snd i)) 
        else fst (snd i)) (S(b x)-a x) 〈b x,x〉.
#a #b #c #p #f #x elim (S(b x)-a x) 
  [normalize //
  |#i #Hind >prim_rec_S
   >fst_pair >snd_pair >snd_pair >fst_pair >snd_pair >fst_pair
   cases (true_or_false (p 〈b x - i,x〉)) #Hcase >Hcase
    [<Hind >bigop_Strue // |<Hind >bigop_Sfalse // ]
  ]
qed.

(*
lemma bigop_aux_1: ∀k,c,f.
  bigop (S k) (λi:ℕ.true) ? c plus (λi:ℕ.f i) = 
    f 0 + bigop k (λi:ℕ.true) ? c plus (λi:ℕ.f (S i)).
#k #c #f elim k [normalize //] #i #Hind >bigop_Strue //

lemma bigop_prim_rec_dec: ∀a,b,c,f,x.
  bigop (b x-a x) (λi:ℕ.true) ? (c 〈b x,x〉) plus (λi:ℕ.f 〈i+a x,x〉) = 
    prim_rec c 
    (λi. plus (f 〈fst (snd (snd i)) - fst i,snd (snd (snd i))〉) (fst (snd i))) 
    (b x-a x) 〈b x ,x〉.
#a #b #c #f #x normalize elim (b x-a x) 
  [normalize //
  |#i #Hind >prim_rec_S
   >fst_pair >snd_pair >snd_pair >fst_pair >snd_pair >fst_pair
   <Hind >bigop_Strue // |<Hind >bigop_Sfalse // ]
  ]
qed. *)

lemma bigop_plus_c: ∀k,p,f,c.
  c k + bigop k (λi.p i) ? 0 plus (λi.f i) = 
    bigop k (λi.p i) ? (c k) plus (λi.f i).
#k #p #f elim k [normalize //]
#i #Hind #c cases (true_or_false (p i)) #Hcase
[>bigop_Strue // >bigop_Strue // <associative_plus >(commutative_plus ? (f i))
 >associative_plus @eq_f @Hind
|>bigop_Sfalse // >bigop_Sfalse // 
]
qed.

(* the argument is 〈b-a,〈a,x〉〉 *)

(* FG: aliases added by matita compiled with OCaml 4.0.5, bah ??? *)
alias symbol "plus" (instance 3) = "natural plus".
alias symbol "pair" (instance 2) = "abstract pair".
alias id "max" = "cic:/matita/arithmetics/nat/max#def:2".
alias symbol "plus" (instance 5) = "natural plus".
alias symbol "pair" (instance 4) = "abstract pair".
definition max_unary_pr ≝ λp,f.unary_pr (λx.0) 
    (λi. 
      let k ≝ fst i in
      let r ≝ fst (snd i) in
      let a ≝ fst (snd (snd i)) in
      let x ≝ snd (snd (snd i)) in
      if p 〈k + a,x〉 then max (f 〈k+a,x〉) r else r).

lemma max_unary_pr1: ∀a,b,p,f,x.
  max_{i ∈[a x,b x[ | p 〈i,x〉 }(f 〈i,x〉) = 
    ((max_unary_pr p f) ∘ (λx.〈b x - a x,〈a x,x〉〉)) x.
#a #b #p #f #x normalize >fst_pair >snd_pair @max_prim_rec1
qed.

(*
lemma max_unary_pr: ∀a,b,p,f,x.
  max_{i ∈[a,b[ | p 〈i,x〉 }(f 〈i,x〉) = 
    prim_rec (λi.0) 
    (λi.if p 〈fst i +a,x〉 then max (f 〈fst i +a ,snd (snd i)〉) (fst (snd i)) else fst (snd i)) (b-a) x.
*)

(*
definition unary_compl ≝ λp,f,hf.
  unary_pr MSC
   (λx:ℕ
    .fst (snd x)
     +hf
      〈fst x,
      〈unary_pr (λx0:ℕ.O)
       (λi:ℕ
        .(let (k:ℕ) ≝fst i in 
          let (r:ℕ) ≝fst (snd i) in 
          let (a:ℕ) ≝fst (snd (snd i)) in 
          let (x:ℕ) ≝snd (snd (snd i)) in 
          if p 〈k+a,x〉 then max (f 〈k+a,x〉) r else r )) 〈fst x,snd (snd x)〉,
      snd (snd x)〉〉). *)

(* FG: aliases added by matita compiled with OCaml 4.0.5, bah ??? *)   
alias symbol "plus" (instance 6) = "natural plus".
alias symbol "pair" (instance 5) = "abstract pair".
alias symbol "plus" (instance 4) = "natural plus".
alias symbol "pair" (instance 3) = "abstract pair".
alias symbol "plus" (instance 2) = "natural plus".
alias symbol "plus" (instance 1) = "natural plus".
definition aux_compl ≝ λhp,hf.λi.
  let k ≝ fst i in 
  let r ≝ fst (snd i) in 
  let a ≝ fst (snd (snd i)) in 
  let x ≝ snd (snd (snd i)) in 
  hp 〈k+a,x〉 + hf 〈k+a,x〉 + (* was MSC r*) MSC i .
  
definition aux_compl1 ≝ λhp,hf.λi.
  let k ≝ fst i in 
  let r ≝ fst (snd i) in 
  let a ≝ fst (snd (snd i)) in 
  let x ≝ snd (snd (snd i)) in 
  hp 〈k+a,x〉 + hf 〈k+a,x〉 + MSC r.

lemma aux_compl1_def: ∀k,r,m,hp,hf. 
  aux_compl1 hp hf 〈k,〈r,m〉〉 = 
  let a ≝ fst m in 
  let x ≝ snd m in 
  hp 〈k+a,x〉 + hf 〈k+a,x〉 + MSC r.
#k #r #m #hp #hf normalize >fst_pair >snd_pair >snd_pair >fst_pair //
qed.

lemma aux_compl1_def1: ∀k,r,a,x,hp,hf. 
  aux_compl1 hp hf 〈k,〈r,〈a,x〉〉〉 = hp 〈k+a,x〉 + hf 〈k+a,x〉 + MSC r.
#k #r #a #x #hp #hf normalize >fst_pair >snd_pair >snd_pair >fst_pair 
>fst_pair >snd_pair //
qed.

  
axiom Oaux_compl: ∀hp,hf. O (aux_compl1 hp hf) (aux_compl hp hf).
  
(* 
definition IF ≝ λb,f,g:nat →option nat. λx.
  match b x with 
  [None ⇒ None ?
  |Some n ⇒ if (eqb n 0) then f x else g x].
*)

axiom CF_if: ∀b:nat → bool. ∀f,g,s. CF s b → CF s f → CF s g → 
  CF s (λx. if b x then f x else g x).

(*
lemma IF_CF: ∀b,f,g,sb,sf,sg. CF sb b → CF sf f → CF sg g → 
  CF (λn. sb n + sf n + sg n) (IF b f g).
#b #f #g #sb #sf #sg #Hb #Hf #Hg @IF_CF_new
  [@(monotonic_CF … Hb) @O_plus_l @O_plus_l //
  |@(monotonic_CF … Hf) @O_plus_l @O_plus_r //
  |@(monotonic_CF … Hg) @O_plus_r //
  ]
qed.
*)

axiom CF_le: ∀h,f,g. CF h f → CF h g → CF h (λx. leb (f x) (g x)). 
axiom CF_max1: ∀h,f,g. CF h f → CF h g → CF h (λx. max (f x) (g x)). 
axiom CF_plus: ∀h,f,g. CF h f → CF h g → CF h (λx. f x + g x). 
axiom CF_minus: ∀h,f,g. CF h f → CF h g → CF h (λx. f x - g x). 

axiom MSC_prop: ∀f,h. CF h f → ∀x. MSC (f x) ≤ h x.

lemma MSC_max: ∀f,h,x. CF h f → MSC (max_{i < x}(f i)) ≤ max_{i < x}(h i).
#f #h #x #hf elim x // #i #Hind >bigop_Strue [|//] >bigop_Strue [|//]
whd in match (max ??); 
cases (true_or_false (leb (f i) (bigop i (λi0:ℕ.true) ? 0 max(λi0:ℕ.f i0))))
#Hcase >Hcase 
  [@(transitive_le … Hind) @le_maxr //
  |@(transitive_le … (MSC_prop … hf i)) @le_maxl //
  ]
qed.
  
lemma CF_max: ∀a,b.∀p:nat →bool.∀f,ha,hb,hp,hf,s.
  CF ha a → CF hb b → CF hp p → CF hf f → 
  O s (λx.ha x + hb x + 
       (∑_{i ∈[a x ,b x[ }
         (hp 〈i,x〉 + hf 〈i,x〉 + max_{i ∈ [a x, b x [ }(hf 〈i,x〉)))) →
  CF s (λx.max_{i ∈[a x,b x[ | p 〈i,x〉 }(f 〈i,x〉)).
#a #b #p #f #ha #hb #hp #hf #s #CFa #CFb #CFp #CFf #HO 
@ext_CF1 [|#x @max_unary_pr1]
@(CF_comp ??? (λx.ha x + hb x))
  [|@CF_comp_pair
    [@CF_minus [@(O_to_CF … CFb) @O_plus_r // |@(O_to_CF … CFa) @O_plus_l //]
    |@CF_comp_pair 
      [@(O_to_CF … CFa) @O_plus_l // 
      | @(O_to_CF … CF_id) @O_plus_r @(proj1 … CFb)
      ]
    ]
  |@(CF_prim_rec … MSC … (aux_compl1 hp hf))
     [@CF_const
     |@(O_to_CF … (Oaux_compl … ))
      @CF_if 
       [@(CF_comp p … MSC … CFp) 
         [@CF_comp_pair 
           [@CF_plus [@CF_fst| @CF_comp_fst @CF_comp_snd @CF_snd]
           |@CF_comp_snd @CF_comp_snd @CF_snd]
         |@le_to_O #x normalize >commutative_plus >associative_plus @le_plus //
         ]
       |@CF_max1 
         [@(CF_comp f … MSC … CFf) 
           [@CF_comp_pair 
             [@CF_plus [@CF_fst| @CF_comp_fst @CF_comp_snd @CF_snd]
             |@CF_comp_snd @CF_comp_snd @CF_snd]
           |@le_to_O #x normalize >commutative_plus // 
           ]
         |@CF_comp_fst @(monotonic_CF … CF_snd) normalize //
         ]
       |@CF_comp_fst @(monotonic_CF … CF_snd) normalize //
       ]  
     |@O_refl
     ]
  |@(O_trans … HO) -HO
   @(O_trans ? (λx:ℕ
   .ha x+hb x
    +bigop (b x-a x) (λi:ℕ.true) ? (MSC 〈a x,x〉) plus
     (λi:ℕ
      .(λi0:ℕ
        .hp 〈i0,x〉+hf 〈i0,x〉
         +bigop (b x-a x) (λi1:ℕ.true) ? 0 max
          (λi1:ℕ.(λi2:ℕ.hf 〈i2,x〉) (i1+a x))) (i+a x))))
    [
   @le_to_O #n @le_plus // whd in match (unary_pr ???);
   >fst_pair >snd_pair >bigop_prim_rec elim (b n - a n)
    [normalize //
    |#x #Hind >prim_rec_S >fst_pair >snd_pair >fst_pair >snd_pair >aux_compl1_def1
     >prim_rec_S >fst_pair >snd_pair >fst_pair >snd_pair >fst_pair 
     >snd_pair normalize in ⊢ (??%); >commutative_plus @le_plus
      [-Hind @le_plus // normalize >fst_pair >snd_pair 
       @(transitive_le ? (bigop x (λi1:ℕ.true) ? 0 (λn0:ℕ.λm:ℕ.if leb n0 m then m else n0 )
         (λi1:ℕ.hf 〈i1+a n,n〉)))
        [elim x [normalize @MSC_le]
         #x0 #Hind >prim_rec_S >fst_pair >snd_pair >snd_pair >snd_pair
         >fst_pair >fst_pair cases (p 〈x0+a n,n〉) normalize
          [cases (true_or_false (leb (f 〈x0+a n,n〉)
            (prim_rec (λx00:ℕ.O)
             (λi:ℕ
            .if p 〈fst i+fst (snd (snd i)),snd (snd (snd i))〉 
             then if leb (f 〈fst i+fst (snd (snd i)),snd (snd (snd i))〉)
                           (fst (snd i)) 
                      then fst (snd i) 
                      else f 〈fst i+fst (snd (snd i)),snd (snd (snd i))〉  
             else fst (snd i) ) x0 〈a n,n〉))) #Hcase >Hcase normalize
           [@(transitive_le … Hind) -Hind @(le_maxr … (le_n …))
           |@(transitive_le … (MSC_prop … CFf …)) @(le_maxl … (le_n …))
           ]
         |@(transitive_le … Hind) -Hind @(le_maxr … (le_n …))
         ]
       |@(le_maxr … (le_n …))
       ]
     |@(transitive_le … Hind) -Hind 
      generalize in match (bigop x (λi:ℕ.true) ? 0 max
              (λi1:ℕ.(λi2:ℕ.hf 〈i2,n〉) (i1+a n))); #c
      generalize in match (hf 〈x+a n,n〉); #c1
      elim x [//] #x0 #Hind 
      >prim_rec_S >prim_rec_S normalize >fst_pair >fst_pair >snd_pair 
      >snd_pair >snd_pair >snd_pair >snd_pair >snd_pair >fst_pair >fst_pair 
      >fst_pair @le_plus 
       [@le_plus // cases (true_or_false (leb c1 c)) #Hcase 
        >Hcase normalize // @lt_to_le @not_le_to_lt @(leb_false_to_not_le ?? Hcase)
       |@Hind
       ]
     ]
   ]
 |@O_plus [@O_plus_l //] @le_to_O #x 
  <bigop_plus_c @le_plus // @(transitive_le … (MSC_pair …)) @le_plus 
   [@MSC_prop @CFa | @MSC_prop @(O_to_CF MSC … (CF_const x)) @(proj1 … CFb)]
 ]
qed.
       
(* old
axiom CF_max: ∀a,b.∀p:nat →bool.∀f,ha,hb,hp,hf,s.
  CF ha a → CF hb b → CF hp p → CF hf f → 
  O s (λx.ha x + hb x + ∑_{i ∈[a x ,b x[ }(hp 〈i,x〉 + hf 〈i,x〉)) →
  CF s (λx.max_{i ∈[a x,b x[ | p 〈i,x〉 }(f 〈i,x〉)). *)
  
(******************************** minimization ********************************) 

alias symbol "plus" (instance 2) = "natural plus".
alias symbol "plus" (instance 5) = "natural plus".
alias symbol "plus" (instance 1) = "natural plus".
alias symbol "plus" (instance 4) = "natural plus".
alias symbol "pair" (instance 3) = "abstract pair".
alias id "O" = "cic:/matita/arithmetics/nat/nat#con:0:1:0".
let rec my_minim a f x k on k ≝
  match k with
  [O ⇒ a
  |S p ⇒ if eqb (my_minim a f x p) (a+p) 
         then if f 〈a+p,x〉 then a+p else S(a+p)
         else (my_minim a f x p) ].
         
lemma my_minim_S : ∀a,f,x,k. 
  my_minim a f x (S k) = 
    if eqb (my_minim a f x k) (a+k) 
    then if f 〈a+k,x〉 then a+k else S(a+k)
    else (my_minim a f x k) .
// qed.
  
lemma my_minim_fa : ∀a,f,x,k. f〈a,x〉 = true → my_minim a f x k = a.
#a #f #x #k #H elim k // #i #Hind normalize >Hind
cases (true_or_false (eqb a (a+i))) #Hcase >Hcase normalize //
<(eqb_true_to_eq … Hcase) >H //
qed.

lemma my_minim_nfa : ∀a,f,x,k. f〈a,x〉 = false → 
my_minim a f x (S k) = my_minim (S a) f x k.
#a #f #x #k #H elim k  
  [normalize <plus_n_O >H >eq_to_eqb_true // 
  |#i #Hind >my_minim_S >Hind >my_minim_S <plus_n_Sm //
  ]
qed.

lemma my_min_eq : ∀a,f,x,k.
  min k a (λi.f 〈i,x〉) = my_minim a f x k.
#a #f #x #k lapply a -a elim k // #i #Hind #a normalize in ⊢ (??%?);
cases (true_or_false (f 〈a,x〉)) #Hcase >Hcase 
  [>(my_minim_fa … Hcase) // | >Hind @sym_eq @(my_minim_nfa … Hcase) ]
qed.

(* cambiare qui: togliere S *)

(* FG: aliases added by matita compiled with OCaml 4.0.5, bah ??? *)
alias symbol "minus" (instance 1) = "natural minus".
alias symbol "minus" (instance 3) = "natural minus".
alias symbol "pair" (instance 2) = "abstract pair".
definition minim_unary_pr ≝ λf.unary_pr (λx.S(fst x))
    (λi. 
      let k ≝ fst i in
      let r ≝ fst (snd i) in
      let b ≝ fst (snd (snd i)) in
      let x ≝ snd (snd (snd i)) in
      if f 〈b-k,x〉 then b-k else r).
      
definition compl_minim_unary ≝ λhf:nat → nat.λi. 
      let k ≝ fst i in
      let b ≝ fst (snd (snd i)) in
      let x ≝ snd (snd (snd i)) in
      hf 〈b-k,x〉 + MSC 〈k,〈S b,x〉〉.

definition compl_minim_unary_aux ≝ λhf,i. 
      let k ≝ fst i in
      let r ≝ fst (snd i) in
      let b ≝ fst (snd (snd i)) in
      let x ≝ snd (snd (snd i)) in
      hf 〈b-k,x〉 + MSC i.

lemma compl_minim_unary_aux_def : ∀hf,k,r,b,x.
  compl_minim_unary_aux hf 〈k,〈r,〈b,x〉〉〉 = hf 〈b-k,x〉 + MSC 〈k,〈r,〈b,x〉〉〉.
#hf #k #r #b #x normalize >snd_pair >snd_pair >snd_pair >fst_pair >fst_pair //
qed.

lemma compl_minim_unary_def : ∀hf,k,r,b,x.
  compl_minim_unary hf 〈k,〈r,〈b,x〉〉〉 = hf 〈b-k,x〉 + MSC 〈k,〈S b,x〉〉.
#hf #k #r #b #x normalize >snd_pair >snd_pair >snd_pair >fst_pair >fst_pair //
qed.

lemma compl_minim_unary_aux_def2 : ∀hf,k,r,x.
  compl_minim_unary_aux hf 〈k,〈r,x〉〉 = hf 〈fst x-k,snd x〉 + MSC 〈k,〈r,x〉〉.
#hf #k #r #x normalize >snd_pair >snd_pair >fst_pair //
qed.

lemma compl_minim_unary_def2 : ∀hf,k,r,x.
  compl_minim_unary hf 〈k,〈r,x〉〉 = hf 〈fst x-k,snd x〉 + MSC 〈k,〈S(fst x),snd x〉〉.
#hf #k #r #x normalize >snd_pair >snd_pair >fst_pair //
qed.

lemma min_aux: ∀a,f,x,k. min (S k) (a x) (λi:ℕ.f 〈i,x〉) =
  ((minim_unary_pr f) ∘ (λx.〈S k,〈a x + k,x〉〉)) x.
#a #f #x #k whd in ⊢ (???%); >fst_pair >snd_pair
lapply a -a (* @max_prim_rec1 *)
elim k
  [normalize #a >fst_pair >snd_pair >fst_pair >snd_pair >snd_pair >fst_pair 
   <plus_n_O <minus_n_O >fst_pair //
  |#i #Hind #a normalize in ⊢ (??%?); >prim_rec_S >fst_pair >snd_pair
   >fst_pair >snd_pair >snd_pair >fst_pair <plus_n_Sm <(Hind (λx.S (a x)))
   whd in ⊢ (???%); >minus_S_S <(minus_plus_m_m (a x) i) //
qed.

lemma minim_unary_pr1: ∀a,b,f,x.
  μ_{i ∈[a x,b x]}(f 〈i,x〉) = 
    if leb (a x) (b x) then ((minim_unary_pr f) ∘ (λx.〈S (b x) - a x,〈b x,x〉〉)) x
    else (a x).
#a #b #f #x cases (true_or_false (leb (a x) (b x))) #Hcase >Hcase
  [cut (b x = a x + (b x - a x))
    [>commutative_plus <plus_minus_m_m // @leb_true_to_le // ]
   #Hcut whd in ⊢ (???%); >minus_Sn_m [|@leb_true_to_le //]
   >min_aux whd in ⊢ (??%?); <Hcut //
  |>eq_minus_O // @not_le_to_lt @leb_false_to_not_le //
  ]
qed.

axiom sum_inv: ∀a,b,f.∑_{i ∈ [a,S b[ }(f i) = ∑_{i ∈ [a,S b[ }(f (a + b - i)).

(*
#a #b #f @(bigop_iso … plusAC) whd %{(λi.b - a - i)} %{(λi.b - a -i)} %
  [%[#i #lti #_ normalize @eq_f >commutative_plus <plus_minus_associative 
    [2: @le_minus_to_plus_r //
     [// @eq_f @@sym_eq @plus_to_minus 
    |#i #Hi #_ % [% [@le_S_S 
*)

example sum_inv_check : ∑_{i ∈ [3,6[ }(i*i) = ∑_{i ∈ [3,6[ }((8-i)*(8-i)).
normalize // qed.

(* provo rovesciando la somma *)

axiom daemon: ∀P:Prop.P.

lemma CF_mu: ∀a,b.∀f:nat →bool.∀sa,sb,sf,s.
  CF sa a → CF sb b → CF sf f → 
  O s (λx.sa x + sb x + ∑_{i ∈[a x ,S(b x)[ }(sf 〈i,x〉 + MSC 〈b x - i,〈S(b x),x〉〉)) →
  CF s (λx.μ_{i ∈[a x,b x] }(f 〈i,x〉)).
#a #b #f #ha #hb #hf #s #CFa #CFb #CFf #HO 
@ext_CF1 [|#x @minim_unary_pr1]
@CF_if 
  [@CF_le @(O_to_CF … HO) 
    [@(O_to_CF … CFa) @O_plus_l @O_plus_l  @O_refl
    |@(O_to_CF … CFb) @O_plus_l @O_plus_r @O_refl
    ]
  |@(CF_comp ??? (λx.ha x + hb x))
    [|@CF_comp_pair
      [@CF_minus [@CF_compS @(O_to_CF … CFb) @O_plus_r // |@(O_to_CF … CFa) @O_plus_l //]
      |@CF_comp_pair 
        [@(O_to_CF … CFb) @O_plus_r //
        |@(O_to_CF … CF_id) @O_plus_r @(proj1 … CFb)
        ]
      ]
    |@(CF_prim_rec_gen … MSC … (compl_minim_unary_aux hf))
      [@((λx:ℕ.fst (snd x)
          +compl_minim_unary hf
          〈fst x,
          〈unary_pr fst
            (λi:ℕ
             .(let (k:ℕ) ≝fst i in 
               let (r:ℕ) ≝fst (snd i) in 
               let (b:ℕ) ≝fst (snd (snd i)) in 
               let (x:ℕ) ≝snd (snd (snd i)) in if f 〈b-S k,x〉 then b-S k else r ))
          〈fst x,snd (snd x)〉,
          snd (snd x)〉〉))
      |@CF_compS @CF_fst
      |@CF_if 
        [@(CF_comp f … MSC … CFf) 
          [@CF_comp_pair 
            [@CF_minus [@CF_comp_fst @CF_comp_snd @CF_snd|@CF_fst]
            |@CF_comp_snd @CF_comp_snd @CF_snd]
          |@le_to_O #x normalize >commutative_plus //
          ]
        |@(O_to_CF … MSC)
          [@le_to_O #x normalize //
          |@CF_minus
            [@CF_comp_fst @CF_comp_snd @CF_snd |@CF_fst]
          ]
        |@CF_comp_fst @(monotonic_CF … CF_snd) normalize //
        ]
      |@O_plus    
        [@O_plus_l @O_refl 
        |@O_plus_r @O_ext2 [||#x >compl_minim_unary_aux_def2 @refl]
         @O_trans [||@le_to_O #x >compl_minim_unary_def2 @le_n]
         @O_plus [@O_plus_l //] 
         @O_plus_r 
         @O_trans [|@le_to_O #x @MSC_pair] @O_plus 
           [@le_to_O #x @monotonic_MSC @(transitive_le ???? (le_fst …)) 
            >fst_pair @le_n]
         @O_trans [|@le_to_O #x @MSC_pair] @O_plus
           [@le_to_O #x @monotonic_MSC @(transitive_le ???? (le_snd …))
            >snd_pair @(transitive_le ???? (le_fst …)) >fst_pair 
            normalize >snd_pair >fst_pair lapply (surj_pair x)
            * #x1 * #x2 #Hx >Hx >fst_pair >snd_pair elim x1 //
            #i #Hind >prim_rec_S >fst_pair >snd_pair >snd_pair >fst_pair
            cases (f ?) [@le_S // | //]]
         @le_to_O #x @monotonic_MSC @(transitive_le ???? (le_snd …)) >snd_pair
         >(expand_pair (snd (snd x))) in ⊢ (?%?); @le_pair //
        ]
      ] 
    |cut (O s (λx.ha x + hb x + 
            ∑_{i ∈[a x ,S(b x)[ }(hf 〈a x+b x-i,x〉 + MSC 〈b x -(a x+b x-i),〈S(b x),x〉〉)))
      [@(O_ext2 … HO) #x @eq_f @sum_inv] -HO #HO
     @(O_trans … HO) -HO
     @(O_trans ? (λx:ℕ.ha x+hb x
       +bigop (S(b x)-a x) (λi:ℕ.true) ? 
        (MSC 〈b x,x〉) plus (λi:ℕ.(λj.hf j + MSC 〈b x - fst j,〈S(b (snd j)),snd j〉〉) 〈b x- i,x〉)))
      [@le_to_O #n @le_plus // whd in match (unary_pr ???); 
       >fst_pair >snd_pair >(bigop_prim_rec_dec1 a b ? (λi.true)) 
        (* it is crucial to recall that the index is bound by S(b x) *)
        cut (S (b n) - a n ≤ S (b n)) [//]
        elim (S(b n) - a n)
        [normalize //  
        |#x #Hind #lex >prim_rec_S >fst_pair >snd_pair >fst_pair >snd_pair 
         >compl_minim_unary_def >prim_rec_S >fst_pair >snd_pair >fst_pair 
         >snd_pair >fst_pair >snd_pair >fst_pair whd in ⊢ (??%); >commutative_plus 
         @le_plus [2:@Hind @le_S @le_S_S_to_le @lex] -Hind >snd_pair 
         >minus_minus_associative // @le_S_S_to_le // 
        ]
      |@O_plus [@O_plus_l //] @O_ext2 [||#x @bigop_plus_c] 
       @O_plus 
        [@O_plus_l @O_trans [|@le_to_O #x @MSC_pair]
         @O_plus [@O_plus_r @le_to_O @(MSC_prop … CFb)|@O_plus_r @(proj1 … CFb)]
        |@O_plus_r @(O_ext2 … (O_refl …)) #x @same_bigop
          [//|#i #H #_ @eq_f2 [@eq_f @eq_f2 //|>fst_pair @eq_f @eq_f2  //]   
        ]
      ]
    ]
  ] 
  |@(O_to_CF … CFa) @(O_trans … HO) @O_plus_l @O_plus_l @O_refl
  ]
qed.

(*
lemma CF_mu: ∀a,b.∀f:nat →bool.∀sa,sb,sf,s.
  CF sa a → CF sb b → CF sf f → 
  O s (λx.sa x + sb x + ∑_{i ∈[a x ,S(b x)[ }(sf 〈i,x〉)) →
  CF s (λx.μ_{i ∈[a x,b x] }(f 〈i,x〉)).
#a #b #f #ha #hb #hf #s #CFa #CFb #CFf #HO 
@ext_CF1 [|#x @minim_unary_pr1]
@(CF_comp ??? (λx.ha x + hb x))
  [|@CF_comp_pair
    [@CF_minus [@CF_compS @(O_to_CF … CFb) @O_plus_r // |@(O_to_CF … CFa) @O_plus_l //]
    |@CF_comp_pair 
      [@CF_max1 [@(O_to_CF … CFa) @O_plus_l // | @CF_compS @(O_to_CF … CFb) @O_plus_r //]
      | @(O_to_CF … CF_id) @O_plus_r @(proj1 … CFb)
      ]
    ]
  |@(CF_prim_rec … MSC … (compl_minim_unary_aux hf))
    [@CF_fst
    |@CF_if 
      [@(CF_comp f … MSC … CFf) 
        [@CF_comp_pair 
          [@CF_minus [@CF_comp_fst @CF_comp_snd @CF_snd|@CF_compS @CF_fst]
          |@CF_comp_snd @CF_comp_snd @CF_snd]
        |@le_to_O #x normalize >commutative_plus //
        ]
      |@(O_to_CF … MSC)
        [@le_to_O #x normalize //
        |@CF_minus
          [@CF_comp_fst @CF_comp_snd @CF_snd |@CF_compS @CF_fst]
        ]
      |@CF_comp_fst @(monotonic_CF … CF_snd) normalize //
      ]
    |@O_refl
    ]
  |@(O_trans … HO) -HO
   @(O_trans ? (λx:ℕ
   .ha x+hb x
    +bigop (S(b x)-a x) (λi:ℕ.true) ? (MSC 〈a x,x〉) plus (λi:ℕ.hf 〈i+a x,x〉)))
  [@le_to_O #n @le_plus // whd in match (unary_pr ???); 
   >fst_pair >snd_pair >(bigop_prim_rec ? (λn.S(b n)) ? (λi.true)) elim (S(b n) - a n)
    [normalize @monotonic_MSC @le_pair
    |#x #Hind >prim_rec_S >fst_pair >snd_pair >fst_pair >snd_pair >compl_minim_unary_def
     >prim_rec_S >fst_pair >snd_pair >fst_pair >snd_pair >fst_pair 
     >snd_pair normalize in ⊢ (??%); >commutative_plus @le_plus
      [-Hind @le_plus // normalize >fst_pair >snd_pair 
       @(transitive_le ? (bigop x (λi1:ℕ.true) ? 0 (λn0:ℕ.λm:ℕ.if leb n0 m then m else n0 )
         (λi1:ℕ.hf 〈i1+a n,n〉)))
        [elim x [normalize @MSC_le]
         #x0 #Hind >prim_rec_S >fst_pair >snd_pair >snd_pair >snd_pair
         >fst_pair >fst_pair cases (p 〈x0+a n,n〉) normalize
          [cases (true_or_false (leb (f 〈x0+a n,n〉)
            (prim_rec (λx00:ℕ.O)
             (λi:ℕ
            .if p 〈fst i+fst (snd (snd i)),snd (snd (snd i))〉 
             then if leb (f 〈fst i+fst (snd (snd i)),snd (snd (snd i))〉)
                           (fst (snd i)) 
                      then fst (snd i) 
                      else f 〈fst i+fst (snd (snd i)),snd (snd (snd i))〉  
             else fst (snd i) ) x0 〈a n,n〉))) #Hcase >Hcase normalize
           [@(transitive_le … Hind) -Hind @(le_maxr … (le_n …))
           |@(transitive_le … (MSC_prop … CFf …)) @(le_maxl … (le_n …))
           ]
         |@(transitive_le … Hind) -Hind @(le_maxr … (le_n …))
         ]
       |@(le_maxr … (le_n …))
       ]
  
  
   @(O_trans ? (λx:ℕ
   .ha x+hb x
    +bigop (b x-a x) (λi:ℕ.true) ? (MSC 〈a x,x〉) plus
     (λi:ℕ
      .(λi0:ℕ
        .hp 〈i0,x〉+hf 〈i0,x〉
         +bigop (b x-a x) (λi1:ℕ.true) ? 0 max
          (λi1:ℕ.(λi2:ℕ.hf 〈i2,x〉) (i1+a x))) (i+a x))))
    [
   @le_to_O #n @le_plus // whd in match (unary_pr ???);
   >fst_pair >snd_pair >bigop_prim_rec elim (b n - a n)
    [normalize //
    |#x #Hind >prim_rec_S >fst_pair >snd_pair >fst_pair >snd_pair >aux_compl1_def1
     >prim_rec_S >fst_pair >snd_pair >fst_pair >snd_pair >fst_pair 
     >snd_pair normalize in ⊢ (??%); >commutative_plus @le_plus
      [-Hind @le_plus // normalize >fst_pair >snd_pair 
       @(transitive_le ? (bigop x (λi1:ℕ.true) ? 0 (λn0:ℕ.λm:ℕ.if leb n0 m then m else n0 )
         (λi1:ℕ.hf 〈i1+a n,n〉)))
        [elim x [normalize @MSC_le]
         #x0 #Hind >prim_rec_S >fst_pair >snd_pair >snd_pair >snd_pair
         >fst_pair >fst_pair cases (p 〈x0+a n,n〉) normalize
          [cases (true_or_false (leb (f 〈x0+a n,n〉)
            (prim_rec (λx00:ℕ.O)
             (λi:ℕ
            .if p 〈fst i+fst (snd (snd i)),snd (snd (snd i))〉 
             then if leb (f 〈fst i+fst (snd (snd i)),snd (snd (snd i))〉)
                           (fst (snd i)) 
                      then fst (snd i) 
                      else f 〈fst i+fst (snd (snd i)),snd (snd (snd i))〉  
             else fst (snd i) ) x0 〈a n,n〉))) #Hcase >Hcase normalize
           [@(transitive_le … Hind) -Hind @(le_maxr … (le_n …))
           |@(transitive_le … (MSC_prop … CFf …)) @(le_maxl … (le_n …))
           ]
         |@(transitive_le … Hind) -Hind @(le_maxr … (le_n …))
         ]
       |@(le_maxr … (le_n …))
       ]
     |@(transitive_le … Hind) -Hind 
      generalize in match (bigop x (λi:ℕ.true) ? 0 max
              (λi1:ℕ.(λi2:ℕ.hf 〈i2,n〉) (i1+a n))); #c
      generalize in match (hf 〈x+a n,n〉); #c1
      elim x [//] #x0 #Hind 
      >prim_rec_S >prim_rec_S normalize >fst_pair >fst_pair >snd_pair 
      >snd_pair >snd_pair >snd_pair >snd_pair >snd_pair >fst_pair >fst_pair 
      >fst_pair @le_plus 
       [@le_plus // cases (true_or_false (leb c1 c)) #Hcase 
        >Hcase normalize // @lt_to_le @not_le_to_lt @(leb_false_to_not_le ?? Hcase)
       |@Hind
       ]
     ]
   ]
 |@O_plus [@O_plus_l //] @le_to_O #x 
  <bigop_plus_c @le_plus // @(transitive_le … (MSC_pair …)) @le_plus 
   [@MSC_prop @CFa | @MSC_prop @(O_to_CF MSC … (CF_const x)) @(proj1 … CFb)]
 ]
qed.

axiom CF_mu: ∀a,b.∀f:nat →bool.∀sa,sb,sf,s.
  CF sa a → CF sb b → CF sf f → 
  O s (λx.sa x + sb x + ∑_{i ∈[a x ,S(b x)[ }(sf 〈i,x〉)) →
  CF s (λx.μ_{i ∈[a x,b x] }(f 〈i,x〉)).*)
  
(************************************* smn ************************************)
axiom smn: ∀f,s. CF s f → ∀x. CF (λy.s 〈x,y〉) (λy.f 〈x,y〉).

(****************************** constructibility ******************************)
 
definition constructible ≝ λs. CF s s.

lemma constr_comp : ∀s1,s2. constructible s1 → constructible s2 →
  (∀x. x ≤ s2 x) → constructible (s2 ∘ s1).
#s1 #s2 #Hs1 #Hs2 #Hle @(CF_comp … Hs1 Hs2) @O_plus @le_to_O #x [@Hle | //] 
qed.

lemma ext_constr: ∀s1,s2. (∀x.s1 x = s2 x) → 
  constructible s1 → constructible s2.
#s1 #s2 #Hext #Hs1 @(ext_CF … Hext) @(monotonic_CF … Hs1)  #x >Hext //
qed.

lemma constr_prim_rec: ∀s1,s2. constructible s1 → constructible s2 →
  (∀n,r,m. 2 * r ≤ s2 〈n,〈r,m〉〉) → constructible (unary_pr s1 s2).
#s1 #s2 #Hs1 #Hs2 #Hincr @(CF_prim_rec … Hs1 Hs2) whd %{2} %{0} 
#x #_ lapply (surj_pair x) * #a * #b #eqx >eqx whd in match (unary_pr ???); 
>fst_pair >snd_pair
whd in match (unary_pr ???); >fst_pair >snd_pair elim a
  [normalize //
  |#n #Hind >prim_rec_S >fst_pair >snd_pair >fst_pair >snd_pair
   >prim_rec_S @transitive_le [| @(monotonic_le_plus_l … Hind)]
   @transitive_le [| @(monotonic_le_plus_l … (Hincr n ? b))] 
   whd in match (unary_pr ???); >fst_pair >snd_pair //
  ]
qed.

(********************************* simulation *********************************)

axiom sU : nat → nat. 

axiom monotonic_sU: ∀i1,i2,x1,x2,s1,s2. i1 ≤ i2 → x1 ≤ x2 → s1 ≤ s2 →
  sU 〈i1,〈x1,s1〉〉 ≤ sU 〈i2,〈x2,s2〉〉.

lemma monotonic_sU_aux : ∀x1,x2. fst x1 ≤ fst x2 → fst (snd x1) ≤ fst (snd x2) →
snd (snd x1) ≤ snd (snd x2) → sU x1 ≤ sU x2.
#x1 #x2 cases (surj_pair x1) #a1 * #y #eqx1 >eqx1 -eqx1 cases (surj_pair y) 
#b1 * #c1 #eqy >eqy -eqy
cases (surj_pair x2) #a2 * #y2 #eqx2 >eqx2 -eqx2 cases (surj_pair y2) 
#b2 * #c2 #eqy2 >eqy2 -eqy2 >fst_pair >snd_pair >fst_pair >snd_pair 
>fst_pair >snd_pair >fst_pair >snd_pair @monotonic_sU
qed.
  
axiom sU_le: ∀i,x,s. s ≤ sU 〈i,〈x,s〉〉.
axiom sU_le_i: ∀i,x,s. MSC i ≤ sU 〈i,〈x,s〉〉.
axiom sU_le_x: ∀i,x,s. MSC x ≤ sU 〈i,〈x,s〉〉.

definition pU_unary ≝ λp. pU (fst p) (fst (snd p)) (snd (snd p)).

axiom CF_U : CF sU pU_unary.

definition termb_unary ≝ λx:ℕ.termb (fst x) (fst (snd x)) (snd (snd x)).
definition out_unary ≝ λx:ℕ.out (fst x) (fst (snd x)) (snd (snd x)).

lemma CF_termb: CF sU termb_unary. 
@(ext_CF (fst ∘ pU_unary)) [2: @CF_comp_fst @CF_U]
#n whd in ⊢ (??%?); whd in  ⊢ (??(?%)?); >fst_pair % 
qed.

lemma CF_out: CF sU out_unary. 
@(ext_CF (snd ∘ pU_unary)) [2: @CF_comp_snd @CF_U]
#n whd in ⊢ (??%?); whd in  ⊢ (??(?%)?); >snd_pair % 
qed.


(******************** complexity of g ********************)

(*definition unary_g ≝ λh.λux. g h (fst ux) (snd ux).
definition auxg ≝ 
  λh,ux. max_{i ∈[fst ux,snd ux[ | eqb (min_input h i (snd ux)) (snd ux)} 
    (out i (snd ux) (h (S i) (snd ux))).

lemma compl_g1 : ∀h,s. CF s (auxg h) → CF s (unary_g h).
#h #s #H1 @(CF_compS ? (auxg h) H1) 
qed.

definition aux1g ≝ 
  λh,ux. max_{i ∈[fst ux,snd ux[ | (λp. eqb (min_input h (fst p) (snd (snd p))) (snd (snd p))) 〈i,ux〉} 
    ((λp.out (fst p) (snd (snd p)) (h (S (fst p)) (snd (snd p)))) 〈i,ux〉).

lemma eq_aux : ∀h,x.aux1g h x = auxg h x.
#h #x @same_bigop
  [#n #_ >fst_pair >snd_pair // |#n #_ #_ >fst_pair >snd_pair //]
qed.

lemma compl_g2 : ∀h,s1,s2,s. 
  CF s1
    (λp:ℕ.eqb (min_input h (fst p) (snd (snd p))) (snd (snd p))) →
  CF s2
    (λp:ℕ.out (fst p) (snd (snd p)) (h (S (fst p)) (snd (snd p)))) →
  O s (λx.MSC x + ∑_{i ∈[fst x ,snd x[ }(s1 〈i,x〉+s2 〈i,x〉)) → 
  CF s (auxg h).
#h #s1 #s2 #s #Hs1 #Hs2 #HO @(ext_CF (aux1g h)) 
  [#n whd in ⊢ (??%%); @eq_aux]
@(CF_max … CF_fst CF_snd Hs1 Hs2 …) @(O_trans … HO) 
@O_plus [@O_plus @O_plus_l // | @O_plus_r //]
qed.  

lemma compl_g3 : ∀h,s.
  CF s (λp:ℕ.min_input h (fst p) (snd (snd p))) →
  CF s (λp:ℕ.eqb (min_input h (fst p) (snd (snd p))) (snd (snd p))).
#h #s #H @(CF_eqb … H) @(CF_comp … CF_snd CF_snd) @(O_trans … (proj1 … H))
@O_plus // %{1} %{0} #n #_ >commutative_times <times_n_1 @monotonic_MSC //
qed.

definition min_input_aux ≝ λh,p.
  μ_{y ∈ [S (fst p),snd (snd p)] } 
    ((λx.termb (fst (snd x)) (fst x) (h (S (fst (snd x))) (fst x))) 〈y,p〉). 
    
lemma min_input_eq : ∀h,p. 
    min_input_aux h p  =
    min_input h (fst p) (snd (snd p)).
#h #p >min_input_def whd in ⊢ (??%?); >minus_S_S @min_f_g #i #_ #_ 
whd in ⊢ (??%%); >fst_pair >snd_pair //
qed.

definition termb_aux ≝ λh.
  termb_unary ∘ λp.〈fst (snd p),〈fst p,h (S (fst (snd p))) (fst p)〉〉.

lemma compl_g4 : ∀h,s1,s.
  (CF s1 
    (λp.termb (fst (snd p)) (fst p) (h (S (fst (snd p))) (fst p)))) →
   (O s (λx.MSC x + ∑_{i ∈[S(fst x) ,S(snd (snd x))[ }(s1 〈i,x〉))) →
  CF s (λp:ℕ.min_input h (fst p) (snd (snd p))).
#h #s1 #s #Hs1 #HO @(ext_CF (min_input_aux h))
 [#n whd in ⊢ (??%%); @min_input_eq]
@(CF_mu … MSC MSC … Hs1) 
  [@CF_compS @CF_fst 
  |@CF_comp_snd @CF_snd
  |@(O_trans … HO) @O_plus [@O_plus @O_plus_l // | @O_plus_r //]
qed.*)

(************************* a couple of technical lemmas ***********************)
lemma minus_to_0: ∀a,b. a ≤ b → minus a b = 0.
#a elim a // #n #Hind * 
  [#H @False_ind /2 by absurd/ | #b normalize #H @Hind @le_S_S_to_le /2/]
qed.

lemma sigma_bound:  ∀h,a,b. monotonic nat le h → 
  ∑_{i ∈ [a,S b[ }(h i) ≤  (S b-a)*h b.
#h #a #b #H cases (decidable_le a b) 
  [#leab cut (b = pred (S b - a + a)) 
    [<plus_minus_m_m // @le_S //] #Hb >Hb in match (h b);
   generalize in match (S b -a);
   #n elim n 
    [//
    |#m #Hind >bigop_Strue [2://] @le_plus 
      [@H @le_n |@(transitive_le … Hind) @le_times [//] @H //]
    ]
  |#ltba lapply (not_le_to_lt … ltba) -ltba #ltba
   cut (S b -a = 0) [@minus_to_0 //] #Hcut >Hcut //
  ]
qed.

lemma sigma_bound_decr:  ∀h,a,b. (∀a1,a2. a1 ≤ a2 → a2 < b → h a2 ≤ h a1) → 
  ∑_{i ∈ [a,b[ }(h i) ≤  (b-a)*h a.
#h #a #b #H cases (decidable_le a b) 
  [#leab cut ((b -a) +a ≤ b) [/2 by le_minus_to_plus_r/] generalize in match (b -a);
   #n elim n 
    [//
    |#m #Hind >bigop_Strue [2://] #Hm 
     cut (m+a ≤ b) [@(transitive_le … Hm) //] #Hm1
     @le_plus [@H // |@(transitive_le … (Hind Hm1)) //]
    ]
  |#ltba lapply (not_le_to_lt … ltba) -ltba #ltba
   cut (b -a = 0) [@minus_to_0 @lt_to_le @ltba] #Hcut >Hcut //
  ]
qed. 

lemma coroll: ∀s1:nat→nat. (∀n. monotonic ℕ le (λa:ℕ.s1 〈a,n〉)) → 
O (λx.(snd (snd x)-fst x)*(s1 〈snd (snd x),x〉)) 
  (λx.∑_{i ∈[S(fst x) ,S(snd (snd x))[ }(s1 〈i,x〉)).
#s1 #Hs1 %{1} %{0} #n #_ >commutative_times <times_n_1 
@(transitive_le … (sigma_bound …)) [@Hs1|>minus_S_S //]
qed.

lemma coroll2: ∀s1:nat→nat. (∀n,a,b. a ≤ b → b < snd n → s1 〈b,n〉 ≤ s1 〈a,n〉) → 
O (λx.(snd x - fst x)*s1 〈fst x,x〉) (λx.∑_{i ∈[fst x,snd x[ }(s1 〈i,x〉)).
#s1 #Hs1 %{1} %{0} #n #_ >commutative_times <times_n_1 
@(transitive_le … (sigma_bound_decr …)) [2://] @Hs1 
qed.

(**************************** end of technical lemmas *************************)

(*lemma compl_g5 : ∀h,s1.(∀n. monotonic ℕ le (λa:ℕ.s1 〈a,n〉)) →
  (CF s1 
    (λp.termb (fst (snd p)) (fst p) (h (S (fst (snd p))) (fst p)))) →
  CF (λx.MSC x + (snd (snd x)-fst x)*s1 〈snd (snd x),x〉) 
    (λp:ℕ.min_input h (fst p) (snd (snd p))).
#h #s1 #Hmono #Hs1 @(compl_g4 … Hs1) @O_plus 
[@O_plus_l // |@O_plus_r @coroll @Hmono]
qed.

lemma compl_g6: ∀h.
  constructible (λx. h (fst x) (snd x)) →
  (CF (λx. sU 〈max (fst (snd x)) (snd (snd x)),〈fst x,h (S (fst (snd x))) (fst x)〉〉) 
    (λp.termb (fst (snd p)) (fst p) (h (S (fst (snd p))) (fst p)))).
#h #hconstr @(ext_CF (termb_aux h))
  [#n normalize >fst_pair >snd_pair >fst_pair >snd_pair // ]
@(CF_comp … (λx.MSC x + h (S (fst (snd x))) (fst x)) … CF_termb) 
  [@CF_comp_pair
    [@CF_comp_fst @(monotonic_CF … CF_snd) #x //
    |@CF_comp_pair
      [@(monotonic_CF … CF_fst) #x //
      |@(ext_CF ((λx.h (fst x) (snd x))∘(λx.〈S (fst (snd x)),fst x〉)))
        [#n normalize >fst_pair >snd_pair %]
       @(CF_comp … MSC …hconstr)
        [@CF_comp_pair [@CF_compS @CF_comp_fst // |//]
        |@O_plus @le_to_O [//|#n >fst_pair >snd_pair //]
        ]
      ]
    ]
  |@O_plus
    [@O_plus
      [@(O_trans … (λx.MSC (fst x) + MSC (max (fst (snd x)) (snd (snd x))))) 
        [%{2} %{0} #x #_ cases (surj_pair x) #a * #b #eqx >eqx
         >fst_pair >snd_pair @(transitive_le … (MSC_pair …)) 
         >distributive_times_plus @le_plus [//]
         cases (surj_pair b) #c * #d #eqb >eqb
         >fst_pair >snd_pair @(transitive_le … (MSC_pair …)) 
         whd in ⊢ (??%); @le_plus 
          [@monotonic_MSC @(le_maxl … (le_n …)) 
          |>commutative_times <times_n_1 @monotonic_MSC @(le_maxr … (le_n …))  
          ]
        |@O_plus [@le_to_O #x @sU_le_x |@le_to_O #x @sU_le_i]
        ]     
      |@le_to_O #n @sU_le
      ] 
    |@le_to_O #x @monotonic_sU // @(le_maxl … (le_n …)) ]
  ]
qed. *)

definition big : nat →nat ≝ λx. 
  let m ≝ max (fst x) (snd x) in 〈m,m〉.

lemma big_def : ∀a,b. big 〈a,b〉 = 〈max a b,max a b〉.
#a #b normalize >fst_pair >snd_pair // qed.

lemma le_big : ∀x. x ≤ big x. 
#x cases (surj_pair x) #a * #b #eqx >eqx @le_pair >fst_pair >snd_pair 
[@(le_maxl … (le_n …)) | @(le_maxr … (le_n …))]
qed.

definition faux2 ≝ λh.
  (λx.MSC x + (snd (snd x)-fst x)*
    (λx.sU 〈max (fst(snd x)) (snd(snd x)),〈fst x,h (S (fst (snd x))) (fst x)〉〉) 〈snd (snd x),x〉).
 
(*lemma compl_g7: ∀h. 
  constructible (λx. h (fst x) (snd x)) →
  (∀n. monotonic ? le (h n)) → 
  CF (λx.MSC x + (snd (snd x)-fst x)*sU 〈max (fst x) (snd x),〈snd (snd x),h (S (fst x)) (snd (snd x))〉〉)
    (λp:ℕ.min_input h (fst p) (snd (snd p))).
#h #hcostr #hmono @(monotonic_CF … (faux2 h))
  [#n normalize >fst_pair >snd_pair //]
@compl_g5 [2:@(compl_g6 h hcostr)] #n #x #y #lexy >fst_pair >snd_pair 
>fst_pair >snd_pair @monotonic_sU // @hmono @lexy
qed.

lemma compl_g71: ∀h. 
  constructible (λx. h (fst x) (snd x)) →
  (∀n. monotonic ? le (h n)) → 
  CF (λx.MSC (big x) + (snd (snd x)-fst x)*sU 〈max (fst x) (snd x),〈snd (snd x),h (S (fst x)) (snd (snd x))〉〉)
    (λp:ℕ.min_input h (fst p) (snd (snd p))).
#h #hcostr #hmono @(monotonic_CF … (compl_g7 h hcostr hmono)) #x
@le_plus [@monotonic_MSC //]
cases (decidable_le (fst x) (snd(snd x))) 
  [#Hle @le_times // @monotonic_sU  
  |#Hlt >(minus_to_0 … (lt_to_le … )) [// | @not_le_to_lt @Hlt]
  ]
qed.*)

definition out_aux ≝ λh.
  out_unary ∘ λp.〈fst p,〈snd(snd p),h (S (fst p)) (snd (snd p))〉〉.

lemma compl_g8: ∀h.
  constructible (λx. h (fst x) (snd x)) →
  (CF (λx. sU 〈max (fst x) (snd x),〈snd(snd x),h (S (fst x)) (snd(snd x))〉〉) 
    (λp.out (fst p) (snd (snd p)) (h (S (fst p)) (snd (snd p))))).
#h #hconstr @(ext_CF (out_aux h))
  [#n normalize >fst_pair >snd_pair >fst_pair >snd_pair // ]
@(CF_comp … (λx.h (S (fst x)) (snd(snd x)) + MSC x) … CF_out) 
  [@CF_comp_pair
    [@(monotonic_CF … CF_fst) #x //
    |@CF_comp_pair
      [@CF_comp_snd @(monotonic_CF … CF_snd) #x //
      |@(ext_CF ((λx.h (fst x) (snd x))∘(λx.〈S (fst x),snd(snd x)〉)))
        [#n normalize >fst_pair >snd_pair %]
       @(CF_comp … MSC …hconstr)
        [@CF_comp_pair [@CF_compS // | @CF_comp_snd // ]
        |@O_plus @le_to_O [//|#n >fst_pair >snd_pair //]
        ]
      ]
    ]
  |@O_plus 
    [@O_plus 
      [@le_to_O #n @sU_le 
      |@(O_trans … (λx.MSC (max (fst x) (snd x))))
        [%{2} %{0} #x #_ cases (surj_pair x) #a * #b #eqx >eqx
         >fst_pair >snd_pair @(transitive_le … (MSC_pair …)) 
         whd in ⊢ (??%); @le_plus 
          [@monotonic_MSC @(le_maxl … (le_n …)) 
          |>commutative_times <times_n_1 @monotonic_MSC @(le_maxr … (le_n …))  
          ]
        |@le_to_O #x @(transitive_le ???? (sU_le_i … )) //
        ]
      ]
    |@le_to_O #x @monotonic_sU [@(le_maxl … (le_n …))|//|//]
  ]
qed.

(*lemma compl_g9 : ∀h. 
  constructible (λx. h (fst x) (snd x)) →
  (∀n. monotonic ? le (h n)) → 
  (∀n,a,b. a ≤ b → b ≤ n → h b n ≤ h a n) →
  CF (λx. (S (snd x-fst x))*MSC 〈x,x〉 + 
      (snd x-fst x)*(S(snd x-fst x))*sU 〈x,〈snd x,h (S (fst x)) (snd x)〉〉)
   (auxg h).
#h #hconstr #hmono #hantimono 
@(compl_g2 h ??? (compl_g3 … (compl_g71 h hconstr hmono)) (compl_g8 h hconstr))
@O_plus 
  [@O_plus_l @le_to_O #x >(times_n_1 (MSC x)) >commutative_times @le_times
    [// | @monotonic_MSC // ]]
@(O_trans … (coroll2 ??))
  [#n #a #b #leab #ltb >fst_pair >fst_pair >snd_pair >snd_pair
   cut (b ≤ n) [@(transitive_le … (le_snd …)) @lt_to_le //] #lebn
   cut (max a n = n) 
    [normalize >le_to_leb_true [//|@(transitive_le … leab lebn)]] #maxa
   cut (max b n = n) [normalize >le_to_leb_true //] #maxb
   @le_plus
    [@le_plus [>big_def >big_def >maxa >maxb //]
     @le_times 
      [/2 by monotonic_le_minus_r/ 
      |@monotonic_sU // @hantimono [@le_S_S // |@ltb] 
      ]
    |@monotonic_sU // @hantimono [@le_S_S // |@ltb]
    ] 
  |@le_to_O #n >fst_pair >snd_pair
   cut (max (fst n) n = n) [normalize >le_to_leb_true //] #Hmax >Hmax
   >associative_plus >distributive_times_plus
   @le_plus [@le_times [@le_S // |>big_def >Hmax //] |//] 
  ]
qed.*)

definition sg ≝ λh,x.
  (S (snd x-fst x))*MSC 〈x,x〉 + (snd x-fst x)*(S(snd x-fst x))*sU 〈x,〈snd x,h (S (fst x)) (snd x)〉〉.

lemma sg_def : ∀h,a,b. 
  sg h 〈a,b〉 = (S (b-a))*MSC 〈〈a,b〉,〈a,b〉〉 + 
   (b-a)*(S(b-a))*sU 〈〈a,b〉,〈b,h (S a) b〉〉.
#h #a #b whd in ⊢ (??%?); >fst_pair >snd_pair // 
qed. 

(*lemma compl_g11 : ∀h.
  constructible (λx. h (fst x) (snd x)) →
  (∀n. monotonic ? le (h n)) → 
  (∀n,a,b. a ≤ b → b ≤ n → h b n ≤ h a n) →
  CF (sg h) (unary_g h).
#h #hconstr #Hm #Ham @compl_g1 @(compl_g9 h hconstr Hm Ham)
qed.*)

(**************************** closing the argument ****************************)

let rec h_of_aux (r:nat →nat) (c,d,b:nat) on d : nat ≝ 
  match d with 
  [ O ⇒ c 
  | S d1 ⇒ (S d)*(MSC 〈〈b-d,b〉,〈b-d,b〉〉) +
     d*(S d)*sU 〈〈b-d,b〉,〈b,r (h_of_aux r c d1 b)〉〉].

lemma h_of_aux_O: ∀r,c,b.
  h_of_aux r c O b  = c.
// qed.

lemma h_of_aux_S : ∀r,c,d,b. 
  h_of_aux r c (S d) b = 
    (S (S d))*(MSC 〈〈b-(S d),b〉,〈b-(S d),b〉〉) + 
      (S d)*(S (S d))*sU 〈〈b-(S d),b〉,〈b,r(h_of_aux r c d b)〉〉.
// qed.

lemma h_of_aux_prim_rec : ∀r,c,n,b. h_of_aux r c n b =
  prim_rec (λx.c) 
   (λx.let d ≝ S(fst x) in 
       let b ≝ snd (snd x) in
       (S d)*(MSC 〈〈b-d,b〉,〈b-d,b〉〉) +
        d*(S d)*sU 〈〈b-d,b〉,〈b,r (fst (snd x))〉〉) n b.
#r #c #n #b elim n
  [>h_of_aux_O normalize //
  |#n1 #Hind >h_of_aux_S >prim_rec_S >snd_pair >snd_pair >fst_pair 
   >fst_pair <Hind //
  ]
qed.

(*
lemma h_of_aux_constr : 
∀r,c. constructible (λx.h_of_aux r c (fst x) (snd x)).
#r #c 
  @(ext_constr … 
    (unary_pr (λx.c) 
     (λx.let d ≝ S(fst x) in 
       let b ≝ snd (snd x) in
       (S d)*(MSC 〈〈b-d,b〉,〈b-d,b〉〉) +
        d*(S d)*sU 〈〈b-d,b〉,〈b,r (fst (snd x))〉〉)))
  [#n @sym_eq whd in match (unary_pr ???); @h_of_aux_prim_rec
  |@constr_prim_rec*)

definition h_of ≝ λr,p. 
  let m ≝ max (fst p) (snd p) in 
  h_of_aux r (MSC 〈〈m,m〉,〈m,m〉〉) (snd p - fst p) (snd p).

lemma h_of_O: ∀r,a,b. b ≤ a → 
  h_of r 〈a,b〉 = let m ≝ max a b in MSC 〈〈m,m〉,〈m,m〉〉.
#r #a #b #Hle normalize >fst_pair >snd_pair >(minus_to_0 … Hle) //
qed.

lemma h_of_def: ∀r,a,b.h_of r 〈a,b〉 = 
  let m ≝ max a b in 
  h_of_aux r (MSC 〈〈m,m〉,〈m,m〉〉) (b - a) b.
#r #a #b normalize >fst_pair >snd_pair //
qed.
  
lemma mono_h_of_aux: ∀r.(∀x. x ≤ r x) → monotonic ? le r →
  ∀d,d1,c,c1,b,b1.c ≤ c1 → d ≤ d1 → b ≤ b1 → 
  h_of_aux r c d b ≤ h_of_aux r c1 d1 b1.
#r #Hr #monor #d #d1 lapply d -d elim d1 
  [#d #c #c1 #b #b1 #Hc #Hd @(le_n_O_elim ? Hd) #leb 
   >h_of_aux_O >h_of_aux_O  //
  |#m #Hind #d #c #c1 #b #b1 #lec #led #leb cases (le_to_or_lt_eq … led)
    [#ltd @(transitive_le … (Hind … lec ? leb)) [@le_S_S_to_le @ltd]
     >h_of_aux_S @(transitive_le ???? (le_plus_n …))
     >(times_n_1 (h_of_aux r c1 m b1)) in ⊢ (?%?); 
     >commutative_times @le_times [//|@(transitive_le … (Hr ?)) @sU_le]
    |#Hd >Hd >h_of_aux_S >h_of_aux_S 
     cut (b-S m ≤ b1 - S m) [/2 by monotonic_le_minus_l/] #Hb1
     @le_plus [@le_times //] 
      [@monotonic_MSC @le_pair @le_pair //
      |@le_times [//] @monotonic_sU 
        [@le_pair // |// |@monor @Hind //]
      ]
    ]
  ]
qed.

lemma mono_h_of2: ∀r.(∀x. x ≤ r x) → monotonic ? le r →
  ∀i,b,b1. b ≤ b1 → h_of r 〈i,b〉 ≤ h_of r 〈i,b1〉.
#r #Hr #Hmono #i #a #b #leab >h_of_def >h_of_def
cut (max i a ≤ max i b)
  [@to_max 
    [@(le_maxl … (le_n …))|@(transitive_le … leab) @(le_maxr … (le_n …))]]
#Hmax @(mono_h_of_aux r Hr Hmono) 
  [@monotonic_MSC @le_pair @le_pair @Hmax |/2 by monotonic_le_minus_l/ |@leab]
qed.

axiom h_of_constr : ∀r:nat →nat. 
  (∀x. x ≤ r x) → monotonic ? le r → constructible r →
  constructible (h_of r).

(*lemma speed_compl: ∀r:nat →nat. 
  (∀x. x ≤ r x) → monotonic ? le r → constructible r →
  CF (h_of r) (unary_g (λi,x. r(h_of r 〈i,x〉))).
#r #Hr #Hmono #Hconstr @(monotonic_CF … (compl_g11 …)) 
  [#x cases (surj_pair x) #a * #b #eqx >eqx 
   >sg_def cases (decidable_le b a)
    [#leba >(minus_to_0 … leba) normalize in ⊢ (?%?);
     <plus_n_O <plus_n_O >h_of_def 
     cut (max a b = a) 
      [normalize cases (le_to_or_lt_eq … leba)
        [#ltba >(lt_to_leb_false … ltba) % 
        |#eqba <eqba >(le_to_leb_true … (le_n ?)) % ]]
     #Hmax >Hmax normalize >(minus_to_0 … leba) normalize
     @monotonic_MSC @le_pair @le_pair //
    |#ltab >h_of_def >h_of_def
     cut (max a b = b) 
      [normalize >(le_to_leb_true … ) [%] @lt_to_le @not_le_to_lt @ltab]
     #Hmax >Hmax 
     cut (max (S a) b = b) 
      [whd in ⊢ (??%?);  >(le_to_leb_true … ) [%] @not_le_to_lt @ltab]
     #Hmax1 >Hmax1
     cut (∃d.b - a = S d) 
       [%{(pred(b-a))} >S_pred [//] @lt_plus_to_minus_r @not_le_to_lt @ltab] 
     * #d #eqd >eqd  
     cut (b-S a = d) [//] #eqd1 >eqd1 >h_of_aux_S >eqd1 
     cut (b - S d = a) 
       [@plus_to_minus >commutative_plus @minus_to_plus 
         [@lt_to_le @not_le_to_lt // | //]] #eqd2 >eqd2
     normalize //
    ]
  |#n #a #b #leab #lebn >h_of_def >h_of_def
   cut (max a n = n) 
    [normalize >le_to_leb_true [%|@(transitive_le … leab lebn)]] #Hmaxa
   cut (max b n = n) 
    [normalize >(le_to_leb_true … lebn) %] #Hmaxb 
   >Hmaxa >Hmaxb @Hmono @(mono_h_of_aux r … Hr Hmono) // /2 by monotonic_le_minus_r/
  |#n #a #b #leab @Hmono @(mono_h_of2 … Hr Hmono … leab)
  |@(constr_comp … Hconstr Hr) @(ext_constr (h_of r))
    [#x cases (surj_pair x) #a * #b #eqx >eqx >fst_pair >snd_pair //]  
   @(h_of_constr r Hr Hmono Hconstr)
  ]
qed.

lemma speed_compl_i: ∀r:nat →nat. 
  (∀x. x ≤ r x) → monotonic ? le r → constructible r →
  ∀i. CF (λx.h_of r 〈i,x〉) (λx.g (λi,x. r(h_of r 〈i,x〉)) i x).
#r #Hr #Hmono #Hconstr #i 
@(ext_CF (λx.unary_g (λi,x. r(h_of r 〈i,x〉)) 〈i,x〉))
  [#n whd in ⊢ (??%%); @eq_f @sym_eq >fst_pair >snd_pair %]
@smn @(ext_CF … (speed_compl r Hr Hmono Hconstr)) #n //
qed.*)

(**************************** the speedup theorem *****************************)
(*theorem pseudo_speedup: 
  ∀r:nat →nat. (∀x. x ≤ r x) → monotonic ? le r → constructible r →
  ∃f.∀sf. CF sf f → ∃g,sg. f ≈ g ∧ CF sg g ∧ O sf (r ∘ sg).
(* ∃m,a.∀n. a≤n → r(sg a) < m * sf n. *)
#r #Hr #Hmono #Hconstr
(* f is (g (λi,x. r(h_of r 〈i,x〉)) 0) *) 
%{(g (λi,x. r(h_of r 〈i,x〉)) 0)} #sf * #H * #i *
#Hcodei #HCi 
(* g is (g (λi,x. r(h_of r 〈i,x〉)) (S i)) *)
%{(g (λi,x. r(h_of r 〈i,x〉)) (S i))}
(* sg is (λx.h_of r 〈i,x〉) *)
%{(λx. h_of r 〈S i,x〉)}
lapply (speed_compl_i … Hr Hmono Hconstr (S i)) #Hg
%[%[@condition_1 |@Hg]
 |cases Hg #H1 * #j * #Hcodej #HCj
  lapply (condition_2 … Hcodei) #Hcond2 (* @not_to_not *)
  cases HCi #m * #a #Ha %{m} %{(max (S i) a)} #n #ltin @lt_to_le @not_le_to_lt 
  @(not_to_not … Hcond2) -Hcond2 #Hlesf %{n} % 
  [@(transitive_le … ltin) @(le_maxl … (le_n …))]
  cases (Ha n ?) [2: @(transitive_le … ltin) @(le_maxr … (le_n …))] 
  #y #Uy %{y} @(monotonic_U … Uy) @(transitive_le … Hlesf) //
 ]
qed.

theorem pseudo_speedup': 
  ∀r:nat →nat. (∀x. x ≤ r x) → monotonic ? le r → constructible r →
  ∃f.∀sf. CF sf f → ∃g,sg. f ≈ g ∧ CF sg g ∧ 
  (* ¬ O (r ∘ sg) sf. *)
  ∃m,a.∀n. a≤n → r(sg a) < m * sf n. 
#r #Hr #Hmono #Hconstr 
(* f is (g (λi,x. r(h_of r 〈i,x〉)) 0) *) 
%{(g (λi,x. r(h_of r 〈i,x〉)) 0)} #sf * #H * #i *
#Hcodei #HCi 
(* g is (g (λi,x. r(h_of r 〈i,x〉)) (S i)) *)
%{(g (λi,x. r(h_of r 〈i,x〉)) (S i))}
(* sg is (λx.h_of r 〈i,x〉) *)
%{(λx. h_of r 〈S i,x〉)}
lapply (speed_compl_i … Hr Hmono Hconstr (S i)) #Hg
%[%[@condition_1 |@Hg]
 |cases Hg #H1 * #j * #Hcodej #HCj
  lapply (condition_2 … Hcodei) #Hcond2 (* @not_to_not *)
  cases HCi #m * #a #Ha
  %{m} %{(max (S i) a)} #n #ltin @not_le_to_lt @(not_to_not … Hcond2) -Hcond2 #Hlesf 
  %{n} % [@(transitive_le … ltin) @(le_maxl … (le_n …))]
  cases (Ha n ?) [2: @(transitive_le … ltin) @(le_maxr … (le_n …))] 
  #y #Uy %{y} @(monotonic_U … Uy) @(transitive_le … Hlesf)
  @Hmono @(mono_h_of2 … Hr Hmono … ltin)
 ]
qed.*)
  
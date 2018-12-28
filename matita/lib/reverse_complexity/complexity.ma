include "reverse_complexity/basics.ma".
include "reverse_complexity/big_O.ma". 

(********************************* complexity *********************************)

(* We assume operations have a minimal structural complexity MSC. 
For instance, for time complexity, MSC is equal to the size of input.
For space complexity, MSC is typically 0, since we only measure the space 
required in addition to dimension of the input. *)

axiom MSC : nat → nat.
axiom MSC_sublinear : ∀n. MSC (S n) ≤ S (MSC n). 
(* axiom MSC_S: O MSC (λx.MSC (S x)) . *)
axiom MSC_le: ∀n. MSC n ≤ n.

axiom monotonic_MSC: monotonic ? le MSC.
axiom MSC_pair_eq: ∀a,b. MSC 〈a,b〉 = MSC a + MSC b.


lemma MSC_pair: ∀a,b. MSC 〈a,b〉 ≤ MSC a + MSC b. // qed.

(* C s i means i is running in O(s) *)
 
definition C ≝ λs,i.∃c.∃a.∀x.a ≤ x → ∃y. 
  U i x (c*(s x)) = Some ? y.

(* C f s means f ∈ O(s) where MSC ∈O(s) *)
definition CF ≝ λs,f.∃i.code_for (total f) i ∧ C s i.

axiom MSC_in: ∀f,h. CF h f → ∀x. MSC x ≤ h x.
axiom MSC_out: ∀f,h. CF h f → ∀x. MSC (f x) ≤ h x.

 
lemma ext_CF : ∀f,g,s. (∀n. f n = g n) → CF s f → CF s g.
#f #g #s #Hext * #i * #Hcode #HC %{i} %
  [#x cases (Hcode x) #a #H %{a} whd in match (total ??); <Hext @H | //] 
qed.

lemma ext_CF1 : ∀f,g,s. (∀n. f n = g n) → CF s g → CF s f.
#f #g #s #Hext * #i * #Hcode #HC %{i} %
  [#x cases (Hcode x) #a #H %{a} whd in match (total ??); >Hext @H | //] 
qed.

lemma monotonic_CF: ∀s1,s2,f.(∀x. s1 x ≤  s2 x) → CF s1 f → CF s2 f.
#s1 #s2 #f #H * #i * #Hcode #Hs1 
%{i} % [//] cases Hs1 #c * #a -Hs1 #Hs1 %{c} %{a} #n #lean 
cases(Hs1 n lean) #y #Hy %{y} @(monotonic_U …Hy) @le_times // 
qed.

lemma O_to_CF: ∀s1,s2,f.O s2 s1 → CF s1 f → CF s2 f.
#s1 #s2 #f #H * #i * #Hcode #Hs1 
%{i} % [//] cases Hs1 #c * #a -Hs1 #Hs1 
cases H #c1 * #a1 #Ha1 %{(c*c1)} %{(a+a1)} #n #lean 
cases(Hs1 n ?) [2:@(transitive_le … lean) //] #y #Hy %{y} @(monotonic_U …Hy)
>associative_times @le_times // @Ha1 @(transitive_le … lean) //
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


(***************************** primitive recursion ****************************)

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

(* with arguments. m is a vector of arguments *)
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
  | S a ⇒ prim_rec_compl k h sk sh a m + sh 〈a,〈prim_rec k h a m,m〉〉].

axiom CF_prim_rec_gen: ∀k,h,sk,sh,sh1. CF sk k → CF sh h →  
  O sh1 (λx. fst (snd x) + 
             sh 〈fst x,〈unary_pr k h 〈fst x,snd (snd x)〉,snd (snd x)〉〉) → 
   CF (unary_pr sk sh1) (unary_pr k h).

lemma CF_prim_rec: ∀k,h,sk,sh,sf. CF sk k → CF sh h → 
  O sf (unary_pr sk 
        (λx. fst (snd x) + 
             sh 〈fst x,〈unary_pr k h 〈fst x,snd (snd x)〉,snd (snd x)〉〉)) 
   → CF sf (unary_pr k h).
#k #h #sk #sh #sf #Hk #Hh #Osf @(O_to_CF … Osf) @(CF_prim_rec_gen … Hk Hh) 
@O_refl
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

(**************************** primitive operations*****************************)

definition id ≝ λx:nat.x.

axiom CF_id: CF MSC id.
axiom CF_const: ∀k.CF MSC (λx.k).
axiom CF_comp_fst: ∀h,f. CF h f → CF h (fst ∘ f).
axiom CF_comp_snd: ∀h,f. CF h f → CF h (snd ∘ f). 
axiom CF_comp_pair: ∀h,f,g. CF h f → CF h g → CF h (λx. 〈f x,g x〉). 

lemma CF_fst: CF MSC fst.
@(ext_CF (fst ∘ id)) [#n //] @(CF_comp_fst … CF_id)
qed.

lemma CF_snd: CF MSC snd.
@(ext_CF (snd ∘ id)) [#n //] @(CF_comp_snd … CF_id)
qed. 

(**************************** arithmetic operations ***************************)

axiom CF_compS: ∀h,f. CF h f → CF h (S ∘ f).
axiom CF_le: ∀h,f,g. CF h f → CF h g → CF h (λx. leb (f x) (g x)). 
axiom CF_eqb: ∀h,f,g. CF h f → CF h g → CF h (λx.eqb (f x) (g x)).
axiom CF_max1: ∀h,f,g. CF h f → CF h g → CF h (λx. max (f x) (g x)). 
axiom CF_plus: ∀h,f,g. CF h f → CF h g → CF h (λx. f x + g x). 
axiom CF_minus: ∀h,f,g. CF h f → CF h g → CF h (λx. f x - g x). 

(******************************** if then else ********************************)

lemma if_prim_rec: ∀b:nat → bool. ∀f,g:nat → nat.∀x:nat.
  if b x then f x else g x = prim_rec g (f ∘ snd ∘ snd) (b x) x.
#b #f #g #x cases (b x) normalize // 
qed.
  
lemma CF_if: ∀b:nat → bool. ∀f,g,s. CF s b → CF s f → CF s g → 
  CF s (λx. if b x then f x else g x).
#b #f #g #s #CFb #CFf #CFg @(ext_CF (λx.unary_pr g (f ∘ snd ∘ snd) 〈b x,x〉))
  [#n @sym_eq normalize >fst_pair >snd_pair @if_prim_rec
  |@(CF_comp ??? s)
    [|@CF_comp_pair // @(O_to_CF … CF_id) @le_to_O @MSC_in // 
    |@(CF_prim_rec_gen ??? (λx.MSC x + s(snd (snd x))) … CFg) [3:@O_refl|] 
     @(CF_comp … (λx.MSC x + s(snd x)) … CF_snd)
      [@(CF_comp … s … CF_snd CFf) @O_refl 
      |@O_plus 
        [@O_plus_l @O_refl
        |@O_plus 
          [@O_plus_l @le_to_O #x @monotonic_MSC //
          |@O_plus_r @O_refl
          ]
        ]
      ]
    |%{6} %{0} #n #_ normalize in ⊢ (??%); <plus_n_O cases (b n) normalize 
      >snd_pair >fst_pair normalize 
      [@le_plus [//] >fst_pair >fst_pair >snd_pair >fst_pair 
       @le_plus [//] >snd_pair >snd_pair >snd_pair >snd_pair 
       <associative_plus <associative_plus @le_plus [|//] 
       @(transitive_le … (MSC_pair …)) >associative_plus @le_plus
        [@(transitive_le ???? (MSC_in … CFf n)) @monotonic_MSC //
        |@(transitive_le … (MSC_pair …)) @le_plus [|@(MSC_in … CFf)]
         normalize @MSC_out @CFg
        ]
      |@le_plus // 
      ]
    ]
  ]
qed.

(********************************* simulation *********************************)

definition pU_unary ≝ λp. pU (fst p) (fst (snd p)) (snd (snd p)).

axiom sU : nat → nat.
axiom CF_U : CF sU pU_unary. 

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
   
axiom sU_pos: ∀x. 0 < sU x.

axiom sU_le: ∀i,x,s. s ≤ sU 〈i,〈x,s〉〉.

lemma sU_le_i: ∀i,x,s. MSC i ≤ sU 〈i,〈x,s〉〉.
#i #x #s @(transitive_le ???? (MSC_in … CF_U 〈i,〈x,s〉〉)) @monotonic_MSC //
qed.

lemma sU_le_x: ∀i,x,s. MSC x ≤ sU 〈i,〈x,s〉〉.
#i #x #s @(transitive_le ???? (MSC_in … CF_U 〈i,〈x,s〉〉)) @monotonic_MSC 
@(transitive_le … 〈x,s〉) //
qed.




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


include "reverse_complexity/complexity.ma".
include "reverse_complexity/sigma_diseq.ma".

include alias "reverse_complexity/basics.ma".

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

lemma sum_prim_rec1: ∀a,b,p,f,x.
  ∑_{i ∈[a x,b x[ | p 〈i,x〉 }(f 〈i,x〉) = 
    prim_rec (λi.0) 
    (λi.if p 〈fst i +fst (snd (snd i)),snd (snd (snd i))〉 
        then f 〈fst i +fst (snd (snd i)),snd (snd (snd i))〉 + fst (snd i) 
        else fst (snd i)) (b x-a x) 〈a x ,x〉.
#a #b #p #f #x elim (b x-a x) 
  [normalize //
  |#i #Hind >prim_rec_S
   >fst_pair >snd_pair >snd_pair >fst_pair >snd_pair >fst_pair
   cases (true_or_false (p 〈i+a x,x〉)) #Hcase >Hcase
    [<Hind >bigop_Strue // |<Hind >bigop_Sfalse // ]
  ]
qed. 

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


(*********************************** maximum **********************************) 

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

(* the argument is 〈b-a,〈a,x〉〉 *)

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

lemma MSC_max: ∀f,h,x. CF h f → MSC (max_{i < x}(f i)) ≤ max_{i < x}(h i).
#f #h #x #hf elim x // #i #Hind >bigop_Strue [|//] >bigop_Strue [|//]
whd in match (max ??); 
cases (true_or_false (leb (f i) (bigop i (λi0:ℕ.true) ? 0 max(λi0:ℕ.f i0))))
#Hcase >Hcase 
  [@(transitive_le … Hind) @le_maxr //
  |@(transitive_le … (MSC_out … hf i)) @le_maxl //
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
      | @(O_to_CF … CF_id) @O_plus_r @le_to_O @(MSC_in … CFb)
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
           |@(transitive_le … (MSC_out … CFf …)) @(le_maxl … (le_n …))
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
   [@MSC_out @CFa | @MSC_out @(O_to_CF MSC … (CF_const x)) @le_to_O @(MSC_in … CFb)]
 ]
qed.

axiom daemon : ∀P:Prop.P.
axiom O_extl: ∀s1,s2,f. (∀x.s1 x = s2 x) → O s1 f → O s2 f.

lemma CF_max2: ∀a,b.∀p:nat →bool.∀f,ha,hb,hp,hf,s.
  CF ha a → CF hb b → CF hp p → CF hf f → 
  O s (λx.ha x + hb x + 
       (b x - a x)*max_{i ∈ [a x, b x [ }(hp 〈i,x〉 + hf 〈i,x〉)) →
  CF s (λx.max_{i ∈[a x,b x[ | p 〈i,x〉 }(f 〈i,x〉)).
#a #b #p #f #ha #hb #hp #hf #s #CFa #CFb #CFp #CFf #Os
@(O_to_CF … Os (CF_max … CFa CFb CFp CFf ?)) @O_plus 
  [@O_plus_l @O_refl
  |@O_plus_r @O_ext2 [|| #x @(bigop_op  … plusAC)]
   @O_plus
    [@le_to_O normalize #x @sigma_to_Max 
    |@le_to_O #x @transitive_le [|@sigma_const] @le_times //  
     @Max_le #i #lti #_ @(transitive_le ???? (le_MaxI … ))
      [@le_plus_n | // | @lt_minus_to_plus_r // | //]
    ]
  ]
qed.

(*
lemma CF_max_monotonic: ∀a,b.∀p:nat →bool.∀f,ha,hb,hp,hf,s.
  CF ha a → CF hb b → CF hp p → CF hf f → 
  O s (λx.ha x + hb x + 
       (b x - a x)*max_{i ∈ [a x, b x [ }(hp 〈i,x〉 + hf 〈i,x〉)) →
  CF s (λx.max_{i ∈[a x,b x[ | p 〈i,x〉 }(f 〈i,x〉)).
#a #b #p #f #ha #hb #hp #hf #s #CFa #CFb #CFp #CFf #Os
@(O_to_CF … Os (CF_max … CFa CFb CFp CFf ?)) @O_plus 
  [@O_plus_l @O_refl
  |@O_plus_r @O_ext2 [|| #x @(bigop_op  … plusAC)]
   @O_plus
    [@le_to_O normalize #x @sigma_to_Max 
    |@le_to_O #x @transitive_le [|@sigma_const] @le_times //  
     @Max_le #i #lti #_ @(transitive_le ???? (le_MaxI … ))
      [@le_plus_n | // | @lt_minus_to_plus_r // | //]
    ]
  ]
qed.
*)

(* old
axiom CF_max: ∀a,b.∀p:nat →bool.∀f,ha,hb,hp,hf,s.
  CF ha a → CF hb b → CF hp p → CF hf f → 
  O s (λx.ha x + hb x + ∑_{i ∈[a x ,b x[ }(hp 〈i,x〉 + hf 〈i,x〉)) →
  CF s (λx.max_{i ∈[a x,b x[ | p 〈i,x〉 }(f 〈i,x〉)). *)
  
(******************************** minimization ********************************) 

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

(* rovesciamo la somma *)

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
        |@(O_to_CF … CF_id) @O_plus_r @le_to_O @(MSC_in … CFb)
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
         @O_plus 
           [@O_plus_r @le_to_O @(MSC_out … CFb)
           |@O_plus_r @le_to_O @(MSC_in … CFb)
           ]
        |@O_plus_r @(O_ext2 … (O_refl …)) #x @same_bigop
          [//|#i #H #_ @eq_f2 [@eq_f @eq_f2 //|>fst_pair @eq_f @eq_f2  //]   
        ]
      ]
    ]
  ] 
  |@(O_to_CF … CFa) @(O_trans … HO) @O_plus_l @O_plus_l @O_refl
  ]
  
qed.

lemma CF_mu2: ∀a,b.∀f:nat →bool.∀sa,sb,sf,s.
  CF sa a → CF sb b → CF sf f → 
  O s (λx.sa x + sb x + ∑_{i ∈[a x ,S(b x)[ }(sf 〈i,x〉 + MSC〈S(b x),x〉)) →
  CF s (λx.μ_{i ∈[a x,b x] }(f 〈i,x〉)).
#a #b #f #sa #sb #sf #s #CFa #CFb #CFf #HO
@(O_to_CF … HO (CF_mu … CFa CFb CFf ?)) @O_plus [@O_plus_l @O_refl] 
@O_plus_r @O_ext2 [|| #x @(bigop_op  … plusAC)]
@O_plus [@le_to_O #x @le_sigma //] 
@(O_trans ? (λx.∑_{i ∈[a x ,S(b x)[ }(MSC(b x -i)+MSC 〈S(b x),x〉))) 
  [@le_to_O #x @le_sigma //]
@O_ext2 [|| #x @(bigop_op  … plusAC)] @O_plus  
  [@le_to_O #x @le_sigma // #i #lti #_ @(transitive_le … (MSC 〈S (b x),x〉)) //
   @monotonic_MSC @(transitive_le … (S(b x))) // @le_S //
  |@le_to_O #x @le_sigma //
  ]
qed.

(* uses MSC_S *)

lemma CF_mu3: ∀a,b.∀f:nat →bool.∀sa,sb,sf,s. (∀x.sf x > 0) →
  CF sa a → CF sb b → CF sf f → 
  O s (λx.sa x + sb x + ∑_{i ∈[a x ,S(b x)[ }(sf 〈i,x〉 + MSC〈b x,x〉)) →
  CF s (λx.μ_{i ∈[a x,b x] }(f 〈i,x〉)).
#a #b #f #sa #sb #sf #s #sfpos #CFa #CFb #CFf #HO
@(O_to_CF … HO (CF_mu2 … CFa CFb CFf ?)) @O_plus [@O_plus_l @O_refl] 
@O_plus_r @O_ext2 [|| #x @(bigop_op  … plusAC)]
@O_plus [@le_to_O #x @le_sigma //] 
@le_to_O #x @le_sigma // #x #lti #_ >MSC_pair_eq >MSC_pair_eq <associative_plus
@le_plus // @(transitive_le … (MSC_sublinear … )) /2 by monotonic_lt_plus_l/
qed.

lemma CF_mu4: ∀a,b.∀f:nat →bool.∀sa,sb,sf,s. (∀x.sf x > 0) →
  CF sa a → CF sb b → CF sf f → 
  O s (λx.sa x + sb x + (S(b x) - a x)*Max_{i ∈[a x ,S(b x)[ }(sf 〈i,x〉)) →
  CF s (λx.μ_{i ∈[a x,b x] }(f 〈i,x〉)).
#a #b #f #sa #sb #sf #s #sfpos #CFa #CFb #CFf #HO
@(O_to_CF … HO (CF_mu3 … sfpos CFa CFb CFf ?)) @O_plus [@O_plus_l @O_refl] 
@O_ext2 [|| #x @(bigop_op  … plusAC)] @O_plus_r @O_plus
  [@le_to_O #x @sigma_to_Max
  |lapply (MSC_in …  CFf) #Hle
   %{1} %{0} #n #_ @(transitive_le … (sigma_const …)) 
   >(commutative_times 1) <times_n_1 
   cases (decidable_le (S (b n)) (a n)) #H
    [>(eq_minus_O … H) //
    |lapply (le_S_S_to_le … (not_le_to_lt … H)) -H #H
     @le_times // @(transitive_le … (Hle … ))
     cut (b n = b n - a n + a n) [<plus_minus_m_m // ]
     #Hcut >Hcut in ⊢ (?%?); @(le_Max (λi.sf 〈i+a n,n〉)) /2/
    ]
  ]
qed.

(*
axiom CF_mu: ∀a,b.∀f:nat →bool.∀sa,sb,sf,s.
  CF sa a → CF sb b → CF sf f → 
  O s (λx.sa x + sb x + ∑_{i ∈[a x ,S(b x)[ }(sf 〈i,x〉)) →
  CF s (λx.μ_{i ∈[a x,b x] }(f 〈i,x〉)). *)
  

  
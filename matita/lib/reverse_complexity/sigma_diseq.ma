include "arithmetics/sigma_pi.ma".

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


(************************* a couple of technical lemmas ***********************)
lemma minus_to_0: ∀a,b. a ≤ b → minus a b = 0.
#a elim a // #n #Hind * 
  [#H @False_ind /2 by absurd/ | #b normalize #H @Hind @le_S_S_to_le /2/]
qed.

lemma sigma_const: ∀c,a,b. 
  ∑_{i ∈ [a,b[ }c ≤  (b-a)*c.
#c #a #b elim (b-a) // #n #Hind normalize @le_plus // 
qed.

lemma sigma_to_Max:  ∀h,a,b. 
  ∑_{i ∈ [a,b[ }(h i) ≤  (b-a)*Max_{i ∈ [a,b[ }(h i).
#h #a #b elim (b-a)
  [//
  |#n #Hind >bigop_Strue [2://] whd in ⊢ (??%);
   @le_plus 
    [>bigop_Strue // @(le_maxl … (le_n …)) 
    |@(transitive_le … Hind) @le_times // >bigop_Strue //
     @(le_maxr … (le_n …))
    ]
  ]
qed.

lemma sigma_bound1:  ∀h,a,b. monotonic nat le h → 
  ∑_{i ∈ [a,b[ }(h i) ≤  (b-a)*h b.
#h #a #b #H 
@(transitive_le … (sigma_to_Max …)) @le_times //
@Max_le #i #lti #_ @H @lt_to_le @lt_minus_to_plus_r //
qed.

lemma sigma_bound_decr1:  ∀h,a,b. (∀a1,a2. a1 ≤ a2 → a2 < b → h a2 ≤ h a1) → 
  ∑_{i ∈ [a,b[ }(h i) ≤  (b-a)*h a.
#h #a #b #H 
@(transitive_le … (sigma_to_Max …)) @le_times //
@Max_le #i #lti #_ @H // @lt_minus_to_plus_r //
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
  
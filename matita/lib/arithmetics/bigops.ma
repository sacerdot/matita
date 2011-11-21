(*
    ||M||  This file is part of HELM, an Hypertextual, Electronic        
    ||A||  Library of Mathematics, developed at the Computer Science     
    ||T||  Department of the University of Bologna, Italy.                     
    ||I||                                                                 
    ||T||  
    ||A||  This file is distributed under the terms of the 
    \   /  GNU General Public License Version 2        
     \ /      
      V_______________________________________________________________ *)

include "basics/types.ma".
include "arithmetics/div_and_mod.ma".

definition sameF_upto: nat → ∀A.relation(nat→A)  ≝
λk.λA.λf,g.∀i. i < k → f i = g i.
     
definition sameF_p: nat → (nat → bool) →∀A.relation(nat→A)  ≝
λk,p,A,f,g.∀i. i < k → p i = true → f i = g i.

lemma sameF_upto_le: ∀A,f,g,n,m. 
 n ≤m → sameF_upto m A f g → sameF_upto n A f g.
#A #f #g #n #m #lenm #samef #i #ltin @samef /2/
qed.

lemma sameF_p_le: ∀A,p,f,g,n,m. 
 n ≤m → sameF_p m p A f g → sameF_p n p A f g.
#A #p #f #g #n #m #lenm #samef #i #ltin #pi @samef /2/
qed.

(*
definition sumF ≝ λA.λf,g:nat → A.λn,i.
if_then_else ? (leb n i) (g (i-n)) (f i). 

lemma sumF_unfold: ∀A,f,g,n,i. 
sumF A f g n i = if_then_else ? (leb n i) (g (i-n)) (f i). 
// qed. *)

definition prodF ≝
 λA,B.λf:nat→A.λg:nat→B.λm,x.〈 f(div x m), g(mod x m) 〉.

(* bigop *)
let rec bigop (n:nat) (p:nat → bool) (B:Type[0])
   (nil: B) (op: B → B → B)  (f: nat → B) ≝
  match n with
   [ O ⇒ nil
   | S k ⇒ 
      match p k with
      [true ⇒ op (f k) (bigop k p B nil op f)
      |false ⇒ bigop k p B nil op f]
   ].
   
notation "\big  [ op , nil ]_{ ident i < n | p } f"
  with precedence 80
for @{'bigop $n $op $nil (λ${ident i}. $p) (λ${ident i}. $f)}.

notation "\big [ op , nil ]_{ ident i < n } f"
  with precedence 80
for @{'bigop $n $op $nil (λ${ident i}.true) (λ${ident i}. $f)}.

interpretation "bigop" 'bigop n op nil p f = (bigop n p ? nil op f).

notation "\big  [ op , nil ]_{ ident j ∈ [a,b[ | p } f"
  with precedence 80
for @{'bigop ($b-$a) $op $nil (λ${ident j}.((λ${ident j}.$p) (${ident j}+$a)))
  (λ${ident j}.((λ${ident j}.$f)(${ident j}+$a)))}.
  
notation "\big  [ op , nil ]_{ ident j ∈ [a,b[ } f"
  with precedence 80
for @{'bigop ($b-$a) $op $nil (λ${ident j}.((λ${ident j}.true) (${ident j}+$a)))
  (λ${ident j}.((λ${ident j}.$f)(${ident j}+$a)))}.  
 
(* notation "\big  [ op , nil ]_{( term 50) a ≤ ident j < b | p } f"
  with precedence 80
for @{\big[$op,$nil]_{${ident j} < ($b-$a) | ((λ${ident j}.$p) (${ident j}+$a))}((λ${ident j}.$f)(${ident j}+$a))}.
*)
 
interpretation "bigop" 'bigop n op nil p f = (bigop n p ? nil op f).
   
lemma bigop_Strue: ∀k,p,B,nil,op.∀f:nat→B. p k = true →
  \big[op,nil]_{i < S k | p i}(f i) =
    op (f k) (\big[op,nil]_{i < k | p i}(f i)).
#k #p #B #nil #op #f #H normalize >H // qed.

lemma bigop_Sfalse: ∀k,p,B,nil,op.∀f:nat→B. p k = false →
  \big[op,nil]_{ i < S k | p i}(f i) =
    \big[op,nil]_{i < k | p i}(f i).
#k #p #B #nil #op #f #H normalize >H // qed. 
 
lemma same_bigop : ∀k,p1,p2,B,nil,op.∀f,g:nat→B. 
  sameF_upto k bool p1 p2 → sameF_p k p1 B f g →
  \big[op,nil]_{i < k | p1 i}(f i) = 
    \big[op,nil]_{i < k | p2 i}(g i).
#k #p1 #p2 #B #nil #op #f #g (elim k) // 
#n #Hind #samep #samef normalize >Hind /2/
<(samep … (le_n …)) cases(true_or_false (p1 n)) #H1 >H1 
normalize // <(samef … (le_n …) H1) // 
qed.

theorem pad_bigop: ∀k,n,p,B,nil,op.∀f:nat→B. n ≤ k → 
\big[op,nil]_{i < n | p i}(f i)
  = \big[op,nil]_{i < k | if_then_else ? (leb n i) false (p i)}(f i).
#k #n #p #B #nil #op #f #lenk (elim lenk) 
  [@same_bigop #i #lti // >(not_le_to_leb_false …) /2/
  |#j #leup #Hind >bigop_Sfalse >(le_to_leb_true … leup) // 
  ] qed.

record Aop (A:Type[0]) (nil:A) : Type[0] ≝
  {op :2> A → A → A; 
   nill:∀a. op nil a = a; 
   nilr:∀a. op a nil = a;
   assoc: ∀a,b,c.op a (op b c) = op (op a b) c
  }.

theorem bigop_sum: ∀k1,k2,p1,p2,B.∀nil.∀op:Aop B nil.∀f,g:nat→B.
op (\big[op,nil]_{i<k1|p1 i}(f i)) \big[op,nil]_{i<k2|p2 i}(g i) =
      \big[op,nil]_{i<k1+k2|if_then_else ? (leb k2 i) (p1 (i-k2)) (p2 i)}
        (if_then_else ? (leb k2 i) (f (i-k2)) (g i)).
#k1 #k2 #p1 #p2 #B #nil #op #f #g (elim k1)
  [normalize >nill @same_bigop #i #lti 
   >(lt_to_leb_false … lti) normalize /2/
  |#i #Hind normalize <minus_plus_m_m (cases (p1 i)) 
   >(le_to_leb_true … (le_plus_n …)) normalize <Hind //
   <assoc //
  ]
qed.

lemma plus_minus1: ∀a,b,c. c ≤ b → a + (b -c) = a + b -c.
#a #b #c #lecb @sym_eq @plus_to_minus >(commutative_plus c)
>associative_plus <plus_minus_m_m //
qed.

theorem bigop_I: ∀n,p,B.∀nil.∀op:Aop B nil.∀f:nat→B.
\big[op,nil]_{i∈[0,n[ |p i}(f i) = \big[op,nil]_{i < n|p i}(f i). 
#n #p #B #nil #op #f <minus_n_O @same_bigop //
qed.
          
theorem bigop_sumI: ∀a,b,c,p,B.∀nil.∀op:Aop B nil.∀f:nat→B.
a ≤ b → b ≤ c →
\big[op,nil]_{i∈[a,c[ |p i}(f i) = 
  op (\big[op,nil]_{i ∈ [b,c[ |p i}(f i)) 
      \big[op,nil]_{i ∈ [a,b[ |p i}(f i).
#a #b # c #p #B #nil #op #f #leab #lebc 
>(plus_minus_m_m (c-a) (b-a)) in ⊢ (??%?); /2/
>minus_plus >(commutative_plus a) <plus_minus_m_m //
>bigop_sum (cut (∀i. b -a ≤ i → i+a = i-(b-a)+b))
  [#i #lei >plus_minus // <plus_minus1 
     [@eq_f @sym_eq @plus_to_minus /2/ | /2/]] 
#H @same_bigop #i #ltic @leb_elim normalize // #lei <H //
qed.   

theorem bigop_a: ∀a,b,B.∀nil.∀op:Aop B nil.∀f:nat→B. a ≤ b →
\big[op,nil]_{i∈[a,S b[ }(f i) = 
  op (\big[op,nil]_{i ∈ [a,b[ }(f (S i))) (f a).
#a #b #B #nil #op #f #leab 
>(bigop_sumI a (S a) (S b)) [|@le_S_S //|//] @eq_f2 
  [@same_bigop // |<minus_Sn_n normalize @nilr]
qed.
  
theorem bigop_0: ∀n,B.∀nil.∀op:Aop B nil.∀f:nat→B.
\big[op,nil]_{i < S n}(f i) = 
  op (\big[op,nil]_{i < n}(f (S i))) (f 0).
#n #B #nil #op #f 
<bigop_I >bigop_a [|//] @eq_f2 [|//] <minus_n_O 
@same_bigop //
qed.    

theorem bigop_prod: ∀k1,k2,p1,p2,B.∀nil.∀op:Aop B nil.∀f: nat →nat → B.
\big[op,nil]_{x<k1|p1 x}(\big[op,nil]_{i<k2|p2 x i}(f x i)) =
  \big[op,nil]_{i<k1*k2|andb (p1 (div i k2)) (p2 (div i k2) (i \mod k2))}
     (f (div i k2) (i \mod k2)).
#k1 #k2 #p1 #p2 #B #nil #op #f (elim k1) //
#n #Hind cases(true_or_false (p1 n)) #Hp1
  [>bigop_Strue // >Hind >bigop_sum @same_bigop
   #i #lti @leb_elim // #lei cut (i = n*k2+(i-n*k2)) /2/
   #eqi [|#H] >eqi in ⊢ (???%);
     >div_plus_times /2/ >Hp1 >(mod_plus_times …) /2/ normalize //
  |>bigop_Sfalse // >Hind >(pad_bigop (S n*k2)) // @same_bigop
   #i #lti @leb_elim // #lei cut (i = n*k2+(i-n*k2)) /2/
   #eqi >eqi in ⊢ (???%); >div_plus_times /2/ 
  ]
qed.

record ACop (A:Type[0]) (nil:A) : Type[0] ≝
  {aop :> Aop A nil; 
   comm: ∀a,b.aop a b = aop b a
  }.
 
lemma bigop_op: ∀k,p,B.∀nil.∀op:ACop B nil.∀f,g: nat → B.
op (\big[op,nil]_{i<k|p i}(f i)) (\big[op,nil]_{i<k|p i}(g i)) =
  \big[op,nil]_{i<k|p i}(op (f i) (g i)).
#k #p #B #nil #op #f #g (elim k) [normalize @nill]
-k #k #Hind (cases (true_or_false (p k))) #H
  [>bigop_Strue // >bigop_Strue // >bigop_Strue //
   normalize <assoc <assoc in ⊢ (???%); @eq_f >assoc >comm in ⊢ (??(????%?)?);
   <assoc @eq_f @Hind
  |>bigop_Sfalse // >bigop_Sfalse // >bigop_Sfalse //
  ]
qed.

lemma bigop_diff: ∀p,B.∀nil.∀op:ACop B nil.∀f:nat → B.∀i,n.
  i < n → p i = true →
  \big[op,nil]_{x<n|p x}(f x)=
    op (f i) (\big[op,nil]_{x<n|andb(notb(eqb i x))(p x)}(f x)).
#p #B #nil #op #f #i #n (elim n) 
  [#ltO @False_ind /2/
  |#n #Hind #lein #pi cases (le_to_or_lt_eq … (le_S_S_to_le …lein)) #Hi
    [cut (andb(notb(eqb i n))(p n) = (p n))
      [>(not_eq_to_eqb_false … (lt_to_not_eq … Hi)) //] #Hcut
     cases (true_or_false (p n)) #pn 
      [>bigop_Strue // >bigop_Strue //
       normalize >assoc >(comm ?? op (f i) (f n)) <assoc >Hind //
      |>bigop_Sfalse // >bigop_Sfalse // >Hind //  
      ]
    |<Hi >bigop_Strue // @eq_f >bigop_Sfalse  
       [@same_bigop // #k #ltki >not_eq_to_eqb_false /2/
       |>eq_to_eqb_true // 
       ]
     ]
   ]
qed.

(* range *)
record range (A:Type[0]): Type[0] ≝
  {enum:nat→A; upto:nat; filter:nat→bool}.
  
definition sub_hk: (nat→nat)→(nat→nat)→∀A:Type[0].relation (range A) ≝
λh,k,A,I,J.∀i.i<(upto A I) → (filter A I i)=true → 
  (h i < upto A J
  ∧ filter A J (h i) = true
  ∧ k (h i) = i).

definition iso: ∀A:Type[0].relation (range A) ≝
  λA,I,J.∃h,k. 
    (∀i. i < (upto A I) → (filter A I i) = true → 
       enum A I i = enum A J (h i)) ∧
    sub_hk h k A I J ∧ sub_hk k h A J I.
  
lemma sub_hkO: ∀h,k,A,I,J. upto A I = 0 → sub_hk h k A I J.
#h #k #A #I #J #up0 #i #lti >up0 @False_ind /2/
qed.

lemma sub0_to_false: ∀h,k,A,I,J. upto A I = 0 → sub_hk h k A J I → 
  ∀i. i < upto A J → filter A J i = false.
#h #k #A #I #J #up0 #sub #i #lti cases(true_or_false (filter A J i)) //
#ptrue (cases (sub i lti ptrue)) * #hi @False_ind /2/ 
qed.

lemma sub_lt: ∀A,e,p,n,m. n ≤ m → 
  sub_hk (λx.x) (λx.x) A (mk_range A e n p) (mk_range A e m p).
#A #e #f #n #m #lenm #i #lti #fi % // % /2/
qed. 

theorem transitive_sub: ∀h1,k1,h2,k2,A,I,J,K. 
  sub_hk h1 k1 A I J → sub_hk h2 k2 A J K → 
    sub_hk (λx.h2(h1 x)) (λx.k1(k2 x)) A I K.
#h1 #k1 #h2 #k2 #A #I #J #K #sub1 #sub2 #i #lti #fi 
cases(sub1 i lti fi) * #lth1i #fh1i #ei 
cases(sub2 (h1 i) lth1i fh1i) * #H1 #H2 #H3 % // % // 
qed. 

theorem bigop_iso: ∀n1,n2,p1,p2,B.∀nil.∀op:ACop B nil.∀f1,f2.
  iso B (mk_range B f1 n1 p1) (mk_range B f2 n2 p2) →
  \big[op,nil]_{i<n1|p1 i}(f1 i) = \big[op,nil]_{i<n2|p2 i}(f2 i).
#n1 #n2 #p1 #p2 #B #nil #op #f1 #f2 * #h * #k * * #same
@(le_gen ? n1) #i lapply p2 (elim i) 
  [(elim n2) // #m #Hind #p2 #_ #sub1 #sub2
   >bigop_Sfalse 
    [@(Hind ? (le_O_n ?)) [/2/ | @(transitive_sub … (sub_lt …) sub2) //]
    |@(sub0_to_false … sub2) //
    ]
  |#n #Hind #p2 #ltn #sub1 #sub2 (cut (n ≤n1)) [/2/] #len
   cases(true_or_false (p1 n)) #p1n
    [>bigop_Strue // (cases (sub1 n (le_n …) p1n)) * #hn #p2hn #eqn
     >(bigop_diff … (h n) n2) // >same // 
     @eq_f @(Hind ? len)
      [#i #ltin #p1i (cases (sub1 i (le_S … ltin) p1i)) * 
       #h1i #p2h1i #eqi % // % // >not_eq_to_eqb_false normalize // 
       @(not_to_not ??? (lt_to_not_eq ? ? ltin)) // 
      |#j #ltj #p2j (cases (sub2 j ltj (andb_true_r …p2j))) * 
       #ltkj #p1kj #eqj % // % // 
       (cases (le_to_or_lt_eq …(le_S_S_to_le …ltkj))) //
       #eqkj @False_ind lapply p2j @eqb_elim 
       normalize /2/
      ]
    |>bigop_Sfalse // @(Hind ? len) 
      [@(transitive_sub … (sub_lt …) sub1) //
      |#i #lti #p2i cases(sub2 i lti p2i) * #ltki #p1ki #eqi
       % // % // cases(le_to_or_lt_eq …(le_S_S_to_le …ltki)) //
       #eqki @False_ind /2/
      ]
    ]
  ]
qed.

(* distributivity *)

record Dop (A:Type[0]) (nil:A): Type[0] ≝
  {sum : ACop A nil; 
   prod: A → A →A;
   null: \forall a. prod a nil = nil; 
   distr: ∀a,b,c:A. prod a (sum b c) = sum (prod a b) (prod a c)
  }.
  
theorem bigop_distr: ∀n,p,B,nil.∀R:Dop B nil.∀f,a.
  let aop ≝ sum B nil R in
  let mop ≝ prod B nil R in
  mop a \big[aop,nil]_{i<n|p i}(f i) = 
   \big[aop,nil]_{i<n|p i}(mop a (f i)).
#n #p #B #nil #R #f #a normalize (elim n) [@null]
#n #Hind (cases (true_or_false (p n))) #H
  [>bigop_Strue // >bigop_Strue // >(distr B nil R) >Hind //
  |>bigop_Sfalse // >bigop_Sfalse //
  ]
qed.
  
(* Sigma e Pi 


notation "Σ_{ ident i < n | p } f"
  with precedence 80
for @{'bigop $n plus 0 (λ${ident i}.p) (λ${ident i}. $f)}.

notation "Σ_{ ident i < n } f"
  with precedence 80
for @{'bigop $n plus 0 (λ${ident i}.true) (λ${ident i}. $f)}.

notation "Σ_{ ident j ∈ [a,b[ } f"
  with precedence 80
for @{'bigop ($b-$a) plus 0 (λ${ident j}.((λ${ident j}.true) (${ident j}+$a)))
  (λ${ident j}.((λ${ident j}.$f)(${ident j}+$a)))}.
  
notation "Σ_{ ident j ∈ [a,b[ | p } f"
  with precedence 80
for @{'bigop ($b-$a) plus 0 (λ${ident j}.((λ${ident j}.$p) (${ident j}+$a)))
  (λ${ident j}.((λ${ident j}.$f)(${ident j}+$a)))}.
 
notation "Π_{ ident i < n | p} f"
  with precedence 80
for @{'bigop $n times 1 (λ${ident i}.$p) (λ${ident i}. $f)}.
 
notation "Π_{ ident i < n } f"
  with precedence 80
for @{'bigop $n times 1 (λ${ident i}.true) (λ${ident i}. $f)}.

notation "Π_{ ident j ∈ [a,b[ } f"
  with precedence 80
for @{'bigop ($b-$a) times 1 (λ${ident j}.((λ${ident j}.true) (${ident j}+$a)))
  (λ${ident j}.((λ${ident j}.$f)(${ident j}+$a)))}.
  
notation "Π_{ ident j ∈ [a,b[ | p } f"
  with precedence 80
for @{'bigop ($b-$a) times 1 (λ${ident j}.((λ${ident j}.$p) (${ident j}+$a)))
  (λ${ident j}.((λ${ident j}.$f)(${ident j}+$a)))}.

*)
(*
    
definition p_ord_times \def
\lambda p,m,x.
  match p_ord x p with
  [pair q r \Rightarrow r*m+q].
  
theorem  eq_p_ord_times: \forall p,m,x.
p_ord_times p m x = (ord_rem x p)*m+(ord x p).
intros.unfold p_ord_times. unfold ord_rem.
unfold ord.
elim (p_ord x p).
reflexivity.
qed.

theorem div_p_ord_times: 
\forall p,m,x. ord x p < m \to p_ord_times p m x / m = ord_rem x p.
intros.rewrite > eq_p_ord_times.
apply div_plus_times.
assumption.
qed.

theorem mod_p_ord_times: 
\forall p,m,x. ord x p < m \to p_ord_times p m x \mod m = ord x p.
intros.rewrite > eq_p_ord_times.
apply mod_plus_times.
assumption.
qed.

lemma lt_times_to_lt_O: \forall i,n,m:nat. i < n*m \to O < m.
intros.
elim (le_to_or_lt_eq O ? (le_O_n m))
  [assumption
  |apply False_ind.
   rewrite < H1 in H.
   rewrite < times_n_O in H.
   apply (not_le_Sn_O ? H)
  ]
qed.

theorem iter_p_gen_knm:
\forall A:Type.
\forall baseA: A.
\forall plusA: A \to A \to A. 
(symmetric A plusA) \to 
(associative A plusA) \to 
(\forall a:A.(plusA a  baseA) = a)\to
\forall g: nat \to A.
\forall h2:nat \to nat \to nat.
\forall h11,h12:nat \to nat. 
\forall k,n,m.
\forall p1,p21:nat \to bool.
\forall p22:nat \to nat \to bool.
(\forall x. x < k \to p1 x = true \to 
p21 (h11 x) = true \land p22 (h11 x) (h12 x) = true
\land h2 (h11 x) (h12 x) = x 
\land (h11 x) < n \land (h12 x) < m) \to
(\forall i,j. i < n \to j < m \to p21 i = true \to p22 i j = true \to 
p1 (h2 i j) = true \land 
h11 (h2 i j) = i \land h12 (h2 i j) = j
\land h2 i j < k) \to
iter_p_gen k p1 A g baseA plusA =
iter_p_gen n p21 A (\lambda x:nat.iter_p_gen m (p22 x) A (\lambda y. g (h2 x y)) baseA plusA) baseA plusA.
intros.
rewrite < (iter_p_gen2' n m p21 p22 ? ? ? ? H H1 H2).
apply sym_eq.
apply (eq_iter_p_gen_gh A baseA plusA H H1 H2 g ? (\lambda x.(h11 x)*m+(h12 x)))
 [intros.
  elim (H4 (i/m) (i \mod m));clear H4
   [elim H7.clear H7.
    elim H4.clear H4.
    assumption
   |apply (lt_times_to_lt_div ? ? ? H5)
   |apply lt_mod_m_m.
    apply (lt_times_to_lt_O ? ? ? H5)
   |apply (andb_true_true ? ? H6)
   |apply (andb_true_true_r ? ? H6)
   ]
 |intros.
  elim (H4 (i/m) (i \mod m));clear H4
   [elim H7.clear H7.
    elim H4.clear H4.
    rewrite > H10.
    rewrite > H9.
    apply sym_eq.
    apply div_mod.
    apply (lt_times_to_lt_O ? ? ? H5)
   |apply (lt_times_to_lt_div ? ? ? H5)
   |apply lt_mod_m_m.
    apply (lt_times_to_lt_O ? ? ? H5)  
   |apply (andb_true_true ? ? H6)
   |apply (andb_true_true_r ? ? H6)
   ]
 |intros.
  elim (H4 (i/m) (i \mod m));clear H4
   [elim H7.clear H7.
    elim H4.clear H4.
    assumption
   |apply (lt_times_to_lt_div ? ? ? H5)
   |apply lt_mod_m_m.
    apply (lt_times_to_lt_O ? ? ? H5)
   |apply (andb_true_true ? ? H6)
   |apply (andb_true_true_r ? ? H6)
   ]
 |intros.
  elim (H3 j H5 H6).
  elim H7.clear H7.
  elim H9.clear H9.
  elim H7.clear H7.
  rewrite > div_plus_times
   [rewrite > mod_plus_times
     [rewrite > H9.
      rewrite > H12.
      reflexivity.
     |assumption
     ]
   |assumption
   ]
 |intros.
  elim (H3 j H5 H6).
  elim H7.clear H7.
  elim H9.clear H9.
  elim H7.clear H7. 
  rewrite > div_plus_times
   [rewrite > mod_plus_times
     [assumption
     |assumption
     ]
   |assumption
   ]
 |intros.
  elim (H3 j H5 H6).
  elim H7.clear H7.
  elim H9.clear H9.
  elim H7.clear H7. 
  apply (lt_to_le_to_lt ? ((h11 j)*m+m))
   [apply monotonic_lt_plus_r.
    assumption
   |rewrite > sym_plus.
    change with ((S (h11 j)*m) \le n*m).
    apply monotonic_le_times_l.
    assumption
   ]
 ]
qed.

theorem iter_p_gen_divides:
\forall A:Type.
\forall baseA: A.
\forall plusA: A \to A \to A. 
\forall n,m,p:nat.O < n \to prime p \to Not (divides p n) \to 
\forall g: nat \to A.
(symmetric A plusA) \to (associative A plusA) \to (\forall a:A.(plusA a  baseA) = a)

\to

iter_p_gen (S (n*(exp p m))) (\lambda x.divides_b x (n*(exp p m))) A g baseA plusA =
iter_p_gen (S n) (\lambda x.divides_b x n) A
  (\lambda x.iter_p_gen (S m) (\lambda y.true) A (\lambda y.g (x*(exp p y))) baseA plusA) baseA plusA.
intros.
cut (O < p)
  [rewrite < (iter_p_gen2 ? ? ? ? ? ? ? ? H3 H4 H5).
   apply (trans_eq ? ? 
    (iter_p_gen (S n*S m) (\lambda x:nat.divides_b (x/S m) n) A
       (\lambda x:nat.g (x/S m*(p)\sup(x\mod S m)))  baseA plusA) )
    [apply sym_eq.
     apply (eq_iter_p_gen_gh ? ? ? ? ? ? g ? (p_ord_times p (S m)))
      [ assumption
      | assumption
      | assumption
      |intros.
       lapply (divides_b_true_to_lt_O ? ? H H7).
       apply divides_to_divides_b_true
        [rewrite > (times_n_O O).
         apply lt_times
          [assumption
          |apply lt_O_exp.assumption
          ]
        |apply divides_times
          [apply divides_b_true_to_divides.assumption
          |apply (witness ? ? (p \sup (m-i \mod (S m)))).
           rewrite < exp_plus_times.
           apply eq_f.
           rewrite > sym_plus.
           apply plus_minus_m_m.
           autobatch by le_S_S_to_le, lt_mod_m_m, lt_O_S;
          ]
        ]
      |intros.
       lapply (divides_b_true_to_lt_O ? ? H H7).
       unfold p_ord_times.
       rewrite > (p_ord_exp1 p ? (i \mod (S m)) (i/S m))
        [change with ((i/S m)*S m+i \mod S m=i).
         apply sym_eq.
         apply div_mod.
         apply lt_O_S
        |assumption
        |unfold Not.intro.
         apply H2.
         apply (trans_divides ? (i/ S m))
          [assumption|
           apply divides_b_true_to_divides;assumption]
        |apply sym_times.
        ]
      |intros.
       apply le_S_S.
       apply le_times
        [apply le_S_S_to_le.
         change with ((i/S m) < S n).
         apply (lt_times_to_lt_l m).
         apply (le_to_lt_to_lt ? i);[2:assumption]
         autobatch by eq_plus_to_le, div_mod, lt_O_S.
        |apply le_exp
          [assumption
          |apply le_S_S_to_le.
           apply lt_mod_m_m.
           apply lt_O_S
          ]
        ]
      |intros.
       cut (ord j p < S m)
        [rewrite > div_p_ord_times
          [apply divides_to_divides_b_true
            [apply lt_O_ord_rem
             [elim H1.assumption
             |apply (divides_b_true_to_lt_O ? ? ? H7).
               rewrite > (times_n_O O).
               apply lt_times
               [assumption|apply lt_O_exp.assumption]
             ]
           |cut (n = ord_rem (n*(exp p m)) p)
              [rewrite > Hcut2.
               apply divides_to_divides_ord_rem
                [apply (divides_b_true_to_lt_O ? ? ? H7).
                 rewrite > (times_n_O O).
                 apply lt_times
                 [assumption|apply lt_O_exp.assumption]
                 |rewrite > (times_n_O O).
                   apply lt_times
                  [assumption|apply lt_O_exp.assumption]
               |assumption
               |apply divides_b_true_to_divides.
                assumption
               ]
              |unfold ord_rem.
              rewrite > (p_ord_exp1 p ? m n)
                [reflexivity
               |assumption
                |assumption
               |apply sym_times
               ]
             ]
            ]
          |assumption
          ]
        |cut (m = ord (n*(exp p m)) p)
          [apply le_S_S.
           rewrite > Hcut1.
           apply divides_to_le_ord
            [apply (divides_b_true_to_lt_O ? ? ? H7).
             rewrite > (times_n_O O).
             apply lt_times
              [assumption|apply lt_O_exp.assumption]
            |rewrite > (times_n_O O).
             apply lt_times
              [assumption|apply lt_O_exp.assumption]
            |assumption
            |apply divides_b_true_to_divides.
             assumption
            ]
          |unfold ord.
           rewrite > (p_ord_exp1 p ? m n)
            [reflexivity
            |assumption
            |assumption
            |apply sym_times
            ]
          ]
        ]
      |intros.
       cut (ord j p < S m)
        [rewrite > div_p_ord_times
          [rewrite > mod_p_ord_times
            [rewrite > sym_times.
             apply sym_eq.
             apply exp_ord
              [elim H1.assumption
              |apply (divides_b_true_to_lt_O ? ? ? H7).
               rewrite > (times_n_O O).
               apply lt_times
                [assumption|apply lt_O_exp.assumption]
              ]
           |cut (m = ord (n*(exp p m)) p)
             [apply le_S_S.
              rewrite > Hcut2.
              apply divides_to_le_ord
               [apply (divides_b_true_to_lt_O ? ? ? H7).
                rewrite > (times_n_O O).
                apply lt_times
                 [assumption|apply lt_O_exp.assumption]
               |rewrite > (times_n_O O).
                apply lt_times
                 [assumption|apply lt_O_exp.assumption]
               |assumption
               |apply divides_b_true_to_divides.
                assumption
               ]
             |unfold ord.
              rewrite > (p_ord_exp1 p ? m n)
                [reflexivity
                |assumption
                |assumption
                |apply sym_times
                ]
              ]
            ]
          |assumption
          ]
        |cut (m = ord (n*(exp p m)) p)
          [apply le_S_S.
           rewrite > Hcut1.
           apply divides_to_le_ord
            [apply (divides_b_true_to_lt_O ? ? ? H7).
             rewrite > (times_n_O O).
             apply lt_times
              [assumption|apply lt_O_exp.assumption]
            |rewrite > (times_n_O O).
             apply lt_times
              [assumption|apply lt_O_exp.assumption]
            |assumption
            |apply divides_b_true_to_divides.
             assumption
            ]
          |unfold ord.
           rewrite > (p_ord_exp1 p ? m n)
            [reflexivity
            |assumption
            |assumption
            |apply sym_times
            ]
          ]
        ]
      |intros.
       rewrite > eq_p_ord_times.
       rewrite > sym_plus.
       apply (lt_to_le_to_lt ? (S m +ord_rem j p*S m))
        [apply lt_plus_l.
         apply le_S_S.
         cut (m = ord (n*(p \sup m)) p)
          [rewrite > Hcut1.
           apply divides_to_le_ord
            [apply (divides_b_true_to_lt_O ? ? ? H7).
             rewrite > (times_n_O O).
             apply lt_times
              [assumption|apply lt_O_exp.assumption]
            |rewrite > (times_n_O O).
             apply lt_times
              [assumption|apply lt_O_exp.assumption]
            |assumption
            |apply divides_b_true_to_divides.
             assumption
            ]
          |unfold ord.
           rewrite > sym_times.
           rewrite > (p_ord_exp1 p ? m n)
            [reflexivity
            |assumption
            |assumption
            |reflexivity
            ]
          ]
        |change with (S (ord_rem j p)*S m \le S n*S m).
         apply le_times_l.
         apply le_S_S.
         cut (n = ord_rem (n*(p \sup m)) p)
          [rewrite > Hcut1.
           apply divides_to_le
            [apply lt_O_ord_rem
              [elim H1.assumption
              |rewrite > (times_n_O O).
               apply lt_times
                [assumption|apply lt_O_exp.assumption]
              ]
            |apply divides_to_divides_ord_rem
              [apply (divides_b_true_to_lt_O ? ? ? H7).
               rewrite > (times_n_O O).
               apply lt_times
                [assumption|apply lt_O_exp.assumption]
              |rewrite > (times_n_O O).
               apply lt_times
                [assumption|apply lt_O_exp.assumption]
              |assumption
              |apply divides_b_true_to_divides.
               assumption
              ]
            ]
        |unfold ord_rem.
         rewrite > sym_times.
         rewrite > (p_ord_exp1 p ? m n)
          [reflexivity
          |assumption
          |assumption
          |reflexivity
          ]
        ]
      ]
    ]
  |apply eq_iter_p_gen
  
    [intros.
     elim (divides_b (x/S m) n);reflexivity
    |intros.reflexivity
    ]
  ]
|elim H1.apply lt_to_le.assumption
]
qed.
    


theorem iter_p_gen_2_eq: 
\forall A:Type.
\forall baseA: A.
\forall plusA: A \to A \to A. 
(symmetric A plusA) \to 
(associative A plusA) \to 
(\forall a:A.(plusA a  baseA) = a)\to
\forall g: nat \to nat \to A.
\forall h11,h12,h21,h22: nat \to nat \to nat. 
\forall n1,m1,n2,m2.
\forall p11,p21:nat \to bool.
\forall p12,p22:nat \to nat \to bool.
(\forall i,j. i < n2 \to j < m2 \to p21 i = true \to p22 i j = true \to 
p11 (h11 i j) = true \land p12 (h11 i j) (h12 i j) = true
\land h21 (h11 i j) (h12 i j) = i \land h22 (h11 i j) (h12 i j) = j
\land h11 i j < n1 \land h12 i j < m1) \to
(\forall i,j. i < n1 \to j < m1 \to p11 i = true \to p12 i j = true \to 
p21 (h21 i j) = true \land p22 (h21 i j) (h22 i j) = true
\land h11 (h21 i j) (h22 i j) = i \land h12 (h21 i j) (h22 i j) = j
\land (h21 i j) < n2 \land (h22 i j) < m2) \to
iter_p_gen n1 p11 A 
     (\lambda x:nat .iter_p_gen m1 (p12 x) A (\lambda y. g x y) baseA plusA) 
     baseA plusA =
iter_p_gen n2 p21 A 
    (\lambda x:nat .iter_p_gen m2 (p22 x) A  (\lambda y. g (h11 x y) (h12 x y)) baseA plusA )
    baseA plusA.

intros.
rewrite < (iter_p_gen2' ? ? ? ? ? ? ? ? H H1 H2).
letin ha:= (\lambda x,y.(((h11 x y)*m1) + (h12 x y))).
letin ha12:= (\lambda x.(h21 (x/m1) (x \mod m1))).
letin ha22:= (\lambda x.(h22 (x/m1) (x \mod m1))).

apply (trans_eq ? ? 
(iter_p_gen n2 p21 A (\lambda x:nat. iter_p_gen m2 (p22 x) A
 (\lambda y:nat.(g (((h11 x y)*m1+(h12 x y))/m1) (((h11 x y)*m1+(h12 x y))\mod m1))) baseA plusA ) baseA plusA))
[
  apply (iter_p_gen_knm A baseA plusA H H1 H2 (\lambda e. (g (e/m1) (e \mod m1))) ha ha12 ha22);intros
  [ elim (and_true ? ? H6).
    cut(O \lt m1)
    [ cut(x/m1 < n1)
      [ cut((x \mod m1) < m1)
        [ elim (H4 ? ? Hcut1 Hcut2 H7 H8).
          elim H9.clear H9.
          elim H11.clear H11.
          elim H9.clear H9.
          elim H11.clear H11.
          split
          [ split
            [ split
              [ split
                [ assumption
                | assumption
                ]
              | unfold ha.
                unfold ha12.
                unfold ha22.
                rewrite > H14.
                rewrite > H13.
                apply sym_eq.
                apply div_mod.
                assumption
              ]
            | assumption
            ]
          | assumption
          ]
        | apply lt_mod_m_m.
          assumption
        ]
      | apply (lt_times_n_to_lt m1)
        [ assumption
        | apply (le_to_lt_to_lt ? x)
          [ apply (eq_plus_to_le ? ? (x \mod m1)).
            apply div_mod.
            assumption
          | assumption
        ]
      ]  
    ]
    | apply not_le_to_lt.unfold.intro.
      generalize in match H5.
      apply (le_n_O_elim ? H9).
      rewrite < times_n_O.
      apply le_to_not_lt.
      apply le_O_n.              
    ]
  | elim (H3 ? ? H5 H6 H7 H8).
    elim H9.clear H9.
    elim H11.clear H11.
    elim H9.clear H9.
    elim H11.clear H11.
    cut(((h11 i j)*m1 + (h12 i j))/m1 = (h11 i j))
    [ cut(((h11 i j)*m1 + (h12 i j)) \mod m1 = (h12 i j))
      [ split
        [ split
          [ split
            [ apply true_to_true_to_andb_true
              [ rewrite > Hcut.
                assumption
              | rewrite > Hcut1.
                rewrite > Hcut.
                assumption
              ] 
            | unfold ha.
              unfold ha12.
              rewrite > Hcut1.
              rewrite > Hcut.
              assumption
            ]
          | unfold ha.
            unfold ha22.
            rewrite > Hcut1.
            rewrite > Hcut.
            assumption            
          ]
        | cut(O \lt m1)
          [ cut(O \lt n1)      
            [ apply (lt_to_le_to_lt ? ((h11 i j)*m1 + m1) )
              [ unfold ha.
                apply (lt_plus_r).
                assumption
              | rewrite > sym_plus.
                rewrite > (sym_times (h11 i j) m1).
                rewrite > times_n_Sm.
                rewrite > sym_times.
                apply (le_times_l).
                assumption  
              ]
            | apply not_le_to_lt.unfold.intro.
              generalize in match H12.
              apply (le_n_O_elim ? H11).       
              apply le_to_not_lt.
              apply le_O_n
            ]
          | apply not_le_to_lt.unfold.intro.
            generalize in match H10.
            apply (le_n_O_elim ? H11).       
            apply le_to_not_lt.
            apply le_O_n
          ]  
        ]
      | rewrite > (mod_plus_times m1 (h11 i j) (h12 i j)).
        reflexivity.
        assumption
      ]     
    | rewrite > (div_plus_times m1 (h11 i j) (h12 i j)).
      reflexivity.
      assumption
    ]
  ]
| apply (eq_iter_p_gen1)
  [ intros. reflexivity 
  | intros.
    apply (eq_iter_p_gen1)
    [ intros. reflexivity
    | intros.
      rewrite > (div_plus_times)
      [ rewrite > (mod_plus_times)
        [ reflexivity
        | elim (H3 x x1 H5 H7 H6 H8).
          assumption
        ]
      | elim (H3 x x1 H5 H7 H6 H8).       
        assumption
      ]
    ]
  ]
]
qed.

theorem iter_p_gen_iter_p_gen: 
\forall A:Type.
\forall baseA: A.
\forall plusA: A \to A \to A. 
(symmetric A plusA) \to 
(associative A plusA) \to 
(\forall a:A.(plusA a  baseA) = a)\to
\forall g: nat \to nat \to A.
\forall n,m.
\forall p11,p21:nat \to bool.
\forall p12,p22:nat \to nat \to bool.
(\forall x,y. x < n \to y < m \to 
 (p11 x \land p12 x y) = (p21 y \land p22 y x)) \to
iter_p_gen n p11 A 
  (\lambda x:nat.iter_p_gen m (p12 x) A (\lambda y. g x y) baseA plusA) 
  baseA plusA =
iter_p_gen m p21 A 
  (\lambda y:nat.iter_p_gen n (p22 y) A  (\lambda x. g x y) baseA plusA )
  baseA plusA.
intros.
apply (iter_p_gen_2_eq A baseA plusA H H1 H2 (\lambda x,y. g x y) (\lambda x,y.y) (\lambda x,y.x) (\lambda x,y.y) (\lambda x,y.x)
       n m m n p11 p21 p12 p22)
  [intros.split
    [split
      [split
        [split
          [split
            [apply (andb_true_true ? (p12 j i)).
             rewrite > H3
              [rewrite > H6.rewrite > H7.reflexivity
              |assumption
              |assumption
              ]
            |apply (andb_true_true_r (p11 j)).
             rewrite > H3
              [rewrite > H6.rewrite > H7.reflexivity
              |assumption
              |assumption
              ]
            ]
          |reflexivity
          ]
        |reflexivity
        ]
      |assumption
      ]
    |assumption
    ]
  |intros.split
    [split
      [split
        [split
          [split
            [apply (andb_true_true ? (p22 j i)).
             rewrite < H3
              [rewrite > H6.rewrite > H7.reflexivity
              |assumption
              |assumption
              ]
            |apply (andb_true_true_r (p21 j)).
             rewrite < H3
              [rewrite > H6.rewrite > H7.reflexivity
              |assumption
              |assumption
              ]
            ]
          |reflexivity
          ]
        |reflexivity
        ]
      |assumption
      ]
    |assumption
    ]
  ]
qed. *)
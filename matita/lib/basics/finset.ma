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

include "basics/deqlist.ma".

(****** DeqSet: a set with a decidable equality ******)

record FinSet : Type[1] ≝ 
{ FinSetcarr:> DeqSet;
  enum: list FinSetcarr;
  enum_unique: uniqueb FinSetcarr enum = true;
  enum_complete : ∀x:FinSetcarr. memb ? x enum = true
}.

notation < "𝐅" non associative with precedence 90 
 for @{'bigF}.
interpretation "FinSet" 'bigF = (mk_FinSet ???).

(* bool *)
lemma bool_enum_unique: uniqueb ? [true;false] = true.
// qed.

lemma bool_enum_complete: ∀x:bool. memb ? x [true;false] = true.
* // qed.

definition FinBool ≝ 
  mk_FinSet DeqBool [true;false] bool_enum_unique bool_enum_complete.

unification hint  0 ≔ ; 
    X ≟ FinBool
(* ---------------------------------------- *) ⊢ 
    bool ≡ FinSetcarr X.

(* nat segment *)

lemma eqbnat_true : ∀n,m. eqb n m = true ↔ n = m.
#n #m % [@eqb_true_to_eq | @eq_to_eqb_true]
qed.

definition DeqNat ≝ mk_DeqSet nat eqb eqbnat_true.

lemma lt_to_le : ∀n,m. n < m → n ≤ m.
/2/ qed-.
 
let rec enumnaux n m ≝ 
  match n return (λn.n ≤ m → list (Σx.x < m)) with 
    [ O ⇒ λh.[ ] | S p ⇒ λh:p < m.(mk_Sig ?? p h)::enumnaux p m (lt_to_le p m h)].
    
definition enumn ≝ λn.enumnaux n n (le_n n).

definition Nat_to ≝ λn. DeqSig DeqNat (λi.i<n).

(* lemma prova : ∀n. carr (Nat_to n) = (Σx.x<n). // *)

lemma memb_enumn: ∀m,n,i:DeqNat. ∀h:n ≤ m. ∀k: i < m. n ≤ i →
  (¬ (memb (Nat_to m) (mk_Sig ?? i k) (enumnaux n m h))) = true.
#m #n elim n -n // #n #Hind #i #ltm #k #ltni @sym_eq @noteq_to_eqnot @sym_not_eq
% #H cases (orb_true_l … H)
  [whd in ⊢ (??%?→?); #H1 @(absurd  … ltni) @le_to_not_lt 
   >(eqb_true_to_eq … H1) @le_n
  |<(notb_notb (memb …)) >Hind normalize /2 by lt_to_le, absurd/
  ]
qed. 

lemma enumn_unique_aux: ∀n,m. ∀h:n ≤ m. uniqueb (Nat_to m) (enumnaux n m h) = true.
#n elim n -n // #n #Hind #m #h @true_to_andb_true // @memb_enumn //
qed.
 
lemma enumn_unique: ∀n.uniqueb (Nat_to n) (enumn n) = true.
#n @enumn_unique_aux
qed.

(* definition ltb ≝ λn,m.leb (S n) m. *)
lemma enumn_complete_aux: ∀n,m,i.∀h:n ≤m.∀k:i<m.i<n → 
  memb (Nat_to m) (mk_Sig ?? i k) (enumnaux n m h) = true.
#n elim n -n
  [normalize #n #i #_ #_ #Hfalse @False_ind /2/ 
  |#n #Hind #m #i #h #k #lein whd in ⊢ (??%?);
   cases (le_to_or_lt_eq … (le_S_S_to_le … lein))
    [#ltin cut (eqb (Nat_to m) (mk_Sig ?? i k) (mk_Sig ?? n h) = false)
      [normalize @not_eq_to_eqb_false @lt_to_not_eq @ltin] 
       #Hcut >Hcut @Hind //
    |#eqin cut (eqb (Nat_to m) (mk_Sig ?? i k) (mk_Sig ?? n h) = true)
     [normalize @eq_to_eqb_true //
     |#Hcut >Hcut %
    ]
  ]
qed.

lemma enumn_complete: ∀n.∀i:Nat_to n. memb ? i (enumn n) = true.
#n whd in ⊢ (%→?); * #i #ltin @enumn_complete_aux //
qed.

definition initN ≝ λn.
  mk_FinSet (Nat_to n) (enumn n) (enumn_unique n) (enumn_complete n).

example tipa: ∀n.∃x: initN (S n). pi1 … x = n.
#n @ex_intro [whd @mk_Sig [@n | @le_n] | //] qed.

(* option *)
definition enum_option ≝ λA:DeqSet.λl.
  None A::(map ?? (Some A) l).
  
lemma enum_option_def : ∀A:FinSet.∀l. 
  enum_option A l = None A :: (map ?? (Some A) l).
// qed.

lemma enum_option_unique: ∀A:DeqSet.∀l. 
  uniqueb A l = true → 
    uniqueb ? (enum_option A l) = true.
#A #l #uA @true_to_andb_true
  [generalize in match uA; -uA #_ elim l [%]
   #a #tl #Hind @sym_eq @noteq_to_eqnot % #H 
   cases (orb_true_l … (sym_eq … H))
    [#H1 @(absurd (None A = Some A a)) [@(\P H1) | % #H2 destruct]
    |-H #H >H in Hind; normalize /2/
    ]
  |@unique_map_inj // #a #a1 #H destruct %
  ]
qed.

lemma enum_option_complete: ∀A:DeqSet.∀l. 
  (∀x:A. memb A x l = true) →
    ∀x:DeqOption A. memb ? x (enum_option A l) = true.
#A #l #Hl * // #a @memb_cons @memb_map @Hl
qed.
    
definition FinOption ≝ λA:FinSet.
  mk_FinSet (DeqOption A) 
   (enum_option A (enum A)) 
   (enum_option_unique … (enum_unique A))
   (enum_option_complete … (enum_complete A)).

unification hint  0 ≔ C; 
    T ≟ FinSetcarr C,
    X ≟ FinOption C
(* ---------------------------------------- *) ⊢ 
    option T ≡ FinSetcarr X.

(* sum *)
definition enum_sum ≝ λA,B:DeqSet.λl1.λl2.
  (map ?? (inl A B) l1) @ (map ?? (inr A B) l2).
  
lemma enum_sum_def : ∀A,B:FinSet.∀l1,l2. enum_sum A B l1 l2 = 
  (map ?? (inl A B) l1) @ (map ?? (inr A B) l2).
// qed.

lemma enum_sum_unique: ∀A,B:DeqSet.∀l1,l2. 
  uniqueb A l1 = true → uniqueb B l2 = true → 
    uniqueb ? (enum_sum A B l1 l2) = true.
#A #B #l1 #l2 elim l1 
  [#_ #ul2 @unique_map_inj // #b1 #b2 #Hinr destruct //
  |#a #tl #Hind #uA #uB @true_to_andb_true 
    [@sym_eq @noteq_to_eqnot % #H 
     cases (memb_append … (sym_eq … H))
      [#H1 @(absurd (memb ? a tl = true)) 
        [@(memb_map_inj …H1) #a1 #a2 #Hinl destruct //
        |<(andb_true_l … uA) @eqnot_to_noteq //
        ]
      |elim l2
        [normalize #H destruct 
        |#b #tlB #Hind #membH cases (orb_true_l … membH)
          [#H lapply (\P H) #H1 destruct |@Hind]
        ]
      ] 
    |@Hind // @(andb_true_r … uA)
    ]
  ]
qed.

lemma enum_sum_complete: ∀A,B:DeqSet.∀l1,l2. 
  (∀x:A. memb A x l1 = true) →
  (∀x:B. memb B x l2 = true) →
    ∀x:DeqSum A B. memb ? x (enum_sum A B l1 l2) = true.
#A #B #l1 #l2 #Hl1 #Hl2 *
  [#a @memb_append_l1 @memb_map @Hl1
  |#b @memb_append_l2 @memb_map @Hl2
  ]
qed.
    
definition FinSum ≝ λA,B:FinSet.
  mk_FinSet (DeqSum A B) 
   (enum_sum A B (enum A) (enum B)) 
   (enum_sum_unique … (enum_unique A) (enum_unique B))
   (enum_sum_complete … (enum_complete A) (enum_complete B)).

include alias "basics/types.ma".

unification hint  0 ≔ C1,C2; 
    T1 ≟ FinSetcarr C1,
    T2 ≟ FinSetcarr C2,
    X ≟ FinSum C1 C2
(* ---------------------------------------- *) ⊢ 
    T1+T2 ≡ FinSetcarr X.

(* prod *)

definition enum_prod ≝ λA,B:DeqSet.λl1.λl2.
  compose ??? (mk_Prod A B) l1 l2.

lemma enum_prod_unique: ∀A,B,l1,l2. 
  uniqueb A l1 = true → uniqueb B l2 = true →
  uniqueb ? (enum_prod A B l1 l2) = true.
#A #B #l1 elim l1 //
  #a #tl #Hind #l2 #H1 #H2 @uniqueb_append 
  [@unique_map_inj [#x #y #Heq @(eq_f … \snd … Heq) | //]
  |@Hind // @(andb_true_r … H1)
  |#p #H3 cases (memb_map_to_exists … H3) #b * 
   #Hmemb #eqp <eqp @(not_to_not ? (memb ? a tl = true))
    [2: @sym_not_eq @eqnot_to_noteq @sym_eq @(andb_true_l … H1)
    |elim tl 
      [normalize //
      |#a1 #tl1 #Hind2 #H4 cases (memb_append … H4) -H4 #H4
        [cases (memb_map_to_exists … H4) #b1 * #memb1 #H destruct (H)
         normalize >(\b (refl ? a)) //
        |@orb_true_r2 @Hind2 @H4
        ]
      ]
    ]
  ]
qed.

lemma enum_prod_complete:∀A,B:DeqSet.∀l1,l2.
  (∀a. memb A a l1 = true) → (∀b.memb B b l2 = true) →
    ∀p. memb ? p (enum_prod A B l1 l2) = true.
#A #B #l1 #l2 #Hl1 #Hl2 * #a #b @memb_compose // 
qed.

definition FinProd ≝ 
λA,B:FinSet.mk_FinSet (DeqProd A B)
  (enum_prod A B (enum A) (enum B)) 
  (enum_prod_unique A B … (enum_unique A) (enum_unique B)) 
  (enum_prod_complete A B … (enum_complete A) (enum_complete B)).

unification hint  0 ≔ C1,C2; 
    T1 ≟ FinSetcarr C1,
    T2 ≟ FinSetcarr C2,
    X ≟ FinProd C1 C2
(* ---------------------------------------- *) ⊢ 
    T1×T2 ≡ FinSetcarr X.

(* graph of a function *)

definition graph_of ≝ λA,B.λf:A→B. 
  Σp:A×B.f (\fst p) = \snd p.

definition graph_enum ≝ λA,B:FinSet.λf:A→B. 
  filter ? (λp.f (\fst p) == \snd p) (enum (FinProd A B)).
  
lemma graph_enum_unique : ∀A,B,f.
  uniqueb ? (graph_enum A B f) = true.
#A #B #f @uniqueb_filter @(enum_unique (FinProd A B))
qed.

lemma graph_enum_correct: ∀A,B:FinSet.∀f:A→B. ∀a,b.
memb ? 〈a,b〉 (graph_enum A B f) = true → f a = b.
#A #B #f #a #b #membp @(\P ?) @(filter_true … membp)
qed.

lemma graph_enum_complete: ∀A,B:FinSet.∀f:A→B. ∀a,b.
f a = b → memb ? 〈a,b〉 (graph_enum A B f) = true.
#A #B #f #a #b #eqf @memb_filter_l [@(\b eqf)]
@enum_prod_complete //
qed.

(* FinFun *)
   
definition enum_fun_raw: ∀A,B:DeqSet.list A → list B → list (list (DeqProd A B)) ≝
  λA,B,lA,lB.foldr A (list (list (DeqProd A B))) 
   (λa.compose ??? (λb. cons ? 〈a,b〉) lB) [[]] lA.
   
lemma enum_fun_raw_cons: ∀A,B,a,lA,lB. 
  enum_fun_raw A B (a::lA) lB = 
    compose ??? (λb. cons ? 〈a,b〉) lB (enum_fun_raw A B lA lB).
//
qed.  

definition is_functional ≝ λA,B:DeqSet.λlA:list A.λl: list (DeqProd A B).
  map ?? (fst A B) l = lA.

definition carr_fun ≝ λA,B:FinSet.
  DeqSig (DeqList (DeqProd A B)) (is_functional A B (enum A)).

definition carr_fun_l ≝ λA,B:DeqSet.λl.
  DeqSig (DeqList (DeqProd A B)) (is_functional A B l).

lemma compose_spec1 : ∀A,B,C:DeqSet.∀f:A→B→C.∀a:A.∀b:B.∀lA:list A.∀lB:list B.  
  a ∈ lA = true → b ∈ lB = true → ((f a b) ∈ (compose A B C f lA lB)) = true.
#A #B #C #f #a #b #lA elim lA
  [normalize #lB #H destruct
  |#a1 #tl #Hind #lB #Ha #Hb cases (orb_true_l ?? Ha) #Hcase
    [>(\P Hcase) normalize @memb_append_l1 @memb_map //
    |@memb_append_l2 @Hind //
    ]
  ]
qed.

lemma compose_cons: ∀A,B,C.∀f:A→B→C.∀l1,l2,a.
  compose A B C f (a::l1) l2 =
    (map ?? (f a) l2)@(compose A B C f l1 l2). 
// qed.

lemma compose_spec2 : ∀A,B,C:DeqSet.∀f:A→B→C.∀c:C.∀lA:list A.∀lB:list B.  
  c ∈ (compose A B C f lA lB) = true → 
    ∃a,b.a ∈ lA = true ∧ b ∈ lB = true ∧ c = f a b.
#A #B #C #f #c #lA elim lA
  [normalize #lB #H destruct
  |#a1 #tl #Hind #lB >compose_cons #Hc cases (memb_append … Hc) #Hcase
    [lapply(memb_map_to_exists … Hcase) * #b * #Hb #Hf
     %{a1} %{b} /3/
    |lapply(Hind ? Hcase) * #a2 * #b * * #Ha #Hb #Hf %{a2} %{b} % // % //
     @orb_true_r2 //
    ]
  ]
qed.

definition compose2 ≝ 
  λA,B:DeqSet.λa:A.λl. compose B (carr_fun_l A B l) (carr_fun_l A B (a::l)) 
   (λb,tl. mk_Sig ?? (〈a,b〉::(pi1 … tl)) ?).
normalize @eq_f @(pi2 … tl) 
qed.

let rec Dfoldr (A:Type[0]) (B:list A → Type[0]) 
 (f:∀a:A.∀l.B l → B (a::l)) (b:B [ ]) (l:list A) on l : B l ≝  
 match l with [ nil ⇒ b | cons a l ⇒ f a l (Dfoldr A B f b l)].

definition empty_graph: ∀A,B:DeqSet. carr_fun_l A B []. 
#A #B %{[]} // qed.

definition enum_fun: ∀A,B:DeqSet.∀lA:list A.list B → list (carr_fun_l A B lA) ≝
  λA,B,lA,lB.Dfoldr A (λl.list (carr_fun_l A B l)) 
   (λa,l.compose2 ?? a l lB) [empty_graph A B] lA.

lemma mem_enum_fun: ∀A,B:DeqSet.∀lA,lB.∀x:carr_fun_l A B lA. 
  pi1 … x ∈ map ?? (pi1 … ) (enum_fun A B lA lB) = true → 
  x ∈ enum_fun A B lA lB = true .
#A #B #lA #lB #x @(memb_map_inj  
  (DeqSig (DeqList (DeqProd A B))
   (λx0:DeqList (DeqProd A B).is_functional A B lA x0))
  (DeqList (DeqProd A B)) (pi1 …))
* #l1 #H1 * #l2 #H2 #Heq lapply H1 lapply H2 >Heq // 
qed.
  
lemma enum_fun_cons: ∀A,B,a,lA,lB. 
  enum_fun A B (a::lA) lB = 
    compose ??? (λb,tl. mk_Sig ?? (〈a,b〉::(pi1 … tl)) ?) lB (enum_fun A B lA lB).
//
qed.

lemma map_map: ∀A,B,C.∀f:A→B.∀g:B→C.∀l.
  map ?? g (map ?? f l) =  map ?? (g ∘ f) l.
#A #B #C #f #g #l elim l [//]
#a #tl #Hind normalize @eq_f @Hind
qed.

lemma map_compose: ∀A,B,C,D.∀f:A→B→C.∀g:C→D.∀l1,l2.
  map ?? g (compose A B C f l1 l2) = compose A B D (λa,b. g (f a b)) l1 l2.
#A #B #C #D #f #g #l1 elim l1 [//]
#a #tl #Hind #l2 >compose_cons >compose_cons <map_append @eq_f2
  [@map_map |@Hind]
qed.
   
definition enum_fun_graphs: ∀A,B,lA,lB.
  map ?? (pi1 … ) (enum_fun A B lA lB) = enum_fun_raw A B lA lB.
#A #B #lA elim lA [normalize //]
#a #tl #Hind #lB >(enum_fun_cons A B a tl lB) >enum_fun_raw_cons >map_compose 
cut (∀lB2. compose B (Σx:DeqList (DeqProd A B).is_functional A B tl x)
  (DeqList (DeqProd A B))
  (λa0:B
   .λb:Σx:DeqList (DeqProd A B).is_functional A B tl x
    .〈a,a0〉
     ::pi1 (list (A×B)) (λx:DeqList (DeqProd A B).is_functional A B tl x) b) lB
  (enum_fun A B tl lB2)
  =compose B (list (A×B)) (list (A×B)) (λb:B.cons (A×B) 〈a,b〉) lB
   (enum_fun_raw A B tl lB2))
  [#lB2 elim lB
    [normalize //
    |#b #tlb #Hindb >compose_cons in ⊢ (???%); >compose_cons 
     @eq_f2 [<Hind >map_map // |@Hindb]]] 
#Hcut @Hcut
qed.    

lemma uniqueb_compose: ∀A,B,C:DeqSet.∀f,l1,l2. 
  (∀a1,a2,b1,b2. f a1 b1 = f a2 b2 → a1 = a2 ∧ b1 = b2) →
  uniqueb ? l1 = true → uniqueb ? l2 = true → 
    uniqueb ? (compose A B C f l1 l2) = true.
#A #B #C #f #l1 #l2 #Hinj elim l1 //
#a #tl #Hind #HuA #HuB >compose_cons @uniqueb_append
  [@(unique_map_inj … HuB) #b1 #b2 #Hb1b2 @(proj2 … (Hinj … Hb1b2))
  |@Hind // @(andb_true_r … HuA)
  |#c #Hc lapply(memb_map_to_exists … Hc) * #b * #Hb2 #Hfab % #Hc
   lapply(compose_spec2 … Hc) * #a1 * #b1 * * #Ha1 #Hb1 <Hfab #H
   @(absurd (a=a1)) 
    [@(proj1 … (Hinj … H))
    |% #eqa @(absurd … Ha1) % <eqa #H lapply(andb_true_l … HuA) >H 
     normalize #H1 destruct (H1) 
    ]
  ]
qed.

lemma enum_fun_unique: ∀A,B:DeqSet.∀lA,lB.
    uniqueb ? lA = true → uniqueb ? lB = true →
    uniqueb ? (enum_fun A B lA lB) = true.
#A #B #lA elim lA
  [#lB #_ #ulB //
  |#a #tlA #Hind #lB #uA #uB lapply (enum_fun_cons A B a tlA lB) #H >H
   @(uniqueb_compose B (carr_fun_l A B tlA) (carr_fun_l A B (a::tlA))) 
    [#b1 #b2 * #l1 #funl1 * #l2 #funl2 #H1 destruct (H1) /2/
    |//
    |@(Hind … uB) @(andb_true_r … uA)
    ]
  ]
qed.

lemma enum_fun_complete: ∀A,B:FinSet.∀l1,l2. 
  (∀x:A. memb A x l1 = true) →
  (∀x:B. memb B x l2 = true) →
    ∀x:carr_fun_l A B l1. memb ? x (enum_fun A B l1 l2) = true.
#A #B #l1 #l2 #H1 #H2 * #g #H @mem_enum_fun >enum_fun_graphs 
lapply H -H lapply g -g elim l1  
  [* // #p #tlg normalize #H destruct (H)
  |#a #tl #Hind #g cases g
    [normalize in ⊢ (%→?); #H destruct (H)
    |* #a1 #b #tl1 normalize in ⊢ (%→?); #H
     cut (is_functional A B tl tl1) [destruct (H) //] #Hfun 
     >(cons_injective_l ????? H)
     >(enum_fun_raw_cons … ) @(compose_spec1 … (λb. cons ? 〈a,b〉))
      [@H2 |@Hind @Hfun]
    ]
  ]
qed.
    
definition FinFun ≝ 
λA,B:FinSet.mk_FinSet (carr_fun A B)
  (enum_fun A B (enum A) (enum B)) 
  (enum_fun_unique A B … (enum_unique A) (enum_unique B))
  (enum_fun_complete A B … (enum_complete A) (enum_complete B)).

(*
unification hint  0 ≔ C1,C2; 
    T1 ≟ FinSetcarr C1,
    T2 ≟ FinSetcarr C2,
    X ≟ FinProd C1 C2
(* ---------------------------------------- *) ⊢ 
    T1×T2 ≡ FinSetcarr X. *)
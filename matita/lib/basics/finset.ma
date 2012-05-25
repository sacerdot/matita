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

include "basics/lists/listb.ma".

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
  [#H1 @(absurd … (\P H1)) % #Hfalse
   cut (∀A,P,a,a1,h,h1.mk_Sig A P a h = mk_Sig A P a1 h1 → a = a1)
   [#A #P #a #a1 #h #h1 #H destruct (H) %] #Hcut 
    lapply (Hcut nat (λi.i<m) i n ? ? Hfalse) #Hfalse @(absurd … ltni)
    @le_to_not_lt >Hfalse @le_n
  |<(notb_notb (memb …)) >Hind normalize /2/
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
  
axiom enum_prod_unique: ∀A,B,l1,l2. 
  uniqueb A l1 = true → uniqueb B l2 = true →
  uniqueb ? (enum_prod A B l1 l2) = true.

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


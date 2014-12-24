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

include "basics/finset.ma".
include "basics/star.ma".


inductive FType (O:Type[0]): Type[0] ≝
  | atom : O → FType O 
  | arrow : FType O → FType O → FType O. 

inductive T (O:Type[0]) (D:O → FinSet): Type[0] ≝
  | Val: ∀o:O.carr (D o) → T O D        (* a value in a finset *)
  | Rel: nat → T O D                    (* DB index, base is 0 *)
  | App: T O D → T O D → T O D          (* function, argument *)
  | Lambda: FType O → T O D → T O D     (* type, body *)
  | Vec: FType O → list (T O D) → T O D (* type, body *)
.

let rec FinSet_of_FType O (D:O→FinSet) (ty:FType O) on ty : FinSet ≝
  match ty with
  [atom o ⇒ D o
  |arrow ty1 ty2 ⇒ FinFun (FinSet_of_FType O D ty1) (FinSet_of_FType O D ty2)
  ].

(* size *)

let rec size O D (M:T O D) on M ≝
match M with
  [Val o a ⇒ 1
  |Rel n ⇒ 1
  |App P Q ⇒ size O D P + size O D Q + 1
  |Lambda Ty P ⇒ size O D P + 1
  |Vec Ty v ⇒ foldr ?? (λx,a. size O D x + a) 0 v +1
  ]
.

(* axiom pos_size: ∀M. 1 ≤ size M. *)

theorem Telim_size: ∀O,D.∀P: T O D → Prop. 
 (∀M. (∀N. size O D N < size O D M → P N) → P M) → ∀M. P M.
#O #D #P #H #M (cut (∀p,N. size O D N = p → P N))
  [2: /2/]
#p @(nat_elim1 p) #m #H1 #N #sizeN @H #N0 #Hlt @(H1 (size O D N0)) //
qed.

lemma T_elim: 
  ∀O: Type[0].∀D:O→FinSet.∀P:T O D→Prop.
  (∀o:O.∀x:D o.P (Val O D o x)) →
  (∀n:ℕ.P(Rel O D n)) →
  (∀m,n:T O D.P m→P n→P (App O D m n)) →
  (∀Ty:FType O.∀m:T O D.P m→P(Lambda O D Ty m)) →
  (∀Ty:FType O.∀v:list (T O D).
     (∀x:T O D. mem ? x v → P x) → P(Vec O D Ty v)) →
  ∀x:T O D.P x.
#O #D #P #Hval #Hrel #Happ #Hlam #Hvec @Telim_size #x cases x //
  [ (* app *) #m #n #Hind @Happ @Hind // /2 by le_minus_to_plus/
  | (* lam *) #ty #m #Hind @Hlam @Hind normalize // 
  | (* vec *) #ty #v #Hind @Hvec #x lapply Hind elim v
    [#Hind normalize *
    |#hd #tl #Hind1 #Hind2 * 
      [#Hx >Hx @Hind2 normalize //
      |@Hind1 #N #H @Hind2 @(lt_to_le_to_lt … H) normalize //
      ]
    ]
  ]
qed.
       
        
(* arguments: k is the nesting depth (starts from 0), p is the lift *)
let rec lift O D t k p on t ≝ 
  match t with 
    [ Val o a ⇒ Val O D o a
    | Rel n ⇒ if (leb k n) then Rel O D (n+p) else Rel O D n
    | App m n ⇒ App O D (lift O D m k p) (lift O D n k p)
    | Lambda Ty n ⇒ Lambda O D Ty (lift O D n (S k) p)
    | Vec Ty v ⇒ Vec O D Ty (map ?? (λx. lift O D x k p) v) 
    ].

notation "↑ ^ n ( M )" non associative with precedence 40 for @{'Lift 0 $n $M}.
notation "↑ _ k ^ n ( M )" non associative with precedence 40 for @{'Lift $n $k $M}.

interpretation "Lift" 'Lift n k M = (lift ?? M k n). 

let rec subst O D t k s on t ≝ 
  match t with 
    [ Val o a ⇒ Val O D o a 
    | Rel n ⇒ if (leb k n) then
        (if (eqb k n) then lift O D s 0 n else Rel O D (n-1)) 
        else(Rel O D n)
    | App m n ⇒ App O D (subst O D m k s) (subst O D n k s)
    | Lambda T n ⇒ Lambda O D T (subst O D n (S k) s)
    | Vec T v ⇒ Vec O D T (map ?? (λx. subst O D x k s) v) 
    ].
    
(* notation "hvbox(M break [ k ≝ N ])" 
   non associative with precedence 90
   for @{'Subst1 $M $k $N}. *)
 
interpretation "Subst" 'Subst1 M k N = (subst M k N). 

(* closed terms ????
let rec closed_k O D (t: T O D) k on t ≝ 
  match t with 
    [ Val o a ⇒ True
    | Rel n ⇒ n < k 
    | App m n ⇒ (closed_k O D m k) ∧ (closed_k O D n k)
    | Lambda T n ⇒ closed_k O D n (k+1)
    | Vec T v ⇒ closed_list O D v k
    ]
    
and closed_list O D (l: list (T O D)) k on l ≝
  match l with
    [ nil ⇒ True
    | cons hd tl ⇒ closed_k O D hd k ∧ closed_list O D tl k
    ]
. *)

inductive is_closed (O:Type[0]) (D:O→FinSet): nat → T O D → Prop ≝
| cval : ∀k,o,a.is_closed O D k (Val O D o a)
| cval : ∀k,n. n < k → is_closed O D k (Rel O D n)
| capp : ∀k,n,m. is_closed O D k m → is_closed O D k n → 
           is_closed O D k (App O D m n)
| clam : ∀T,k,m. is_closed O D (k+1) m → is_closed O D k (Lambda O D T m)
| cvec:  ∀T,k,v. (∀m. mem ? m v → is_closed O D k m) → 
           is_closed O D k (Vec O D T v).
           
lemma is_closed_rel: ∀O,D,n,k.
  is_closed O D k (Rel O D n) → n < k.
#O #D #n #k #H inversion H 
  [#k0 #o #a #eqk #H destruct
  |#k0 #n0 #ltn0 #eqk #H destruct //
  |#k0 #M #N #_ #_ #_ #H destruct
  |#T #k0 #M #_ #_ #H destruct
  |#T #k0 #v #_ #_ #H destruct
  ]
qed.
                                   

(*** properties of lift and subst ***)

lemma lift_0: ∀O,D.∀t:T O D.∀k. lift O D t k 0 = t.
#O #D #t @(T_elim … t) normalize // 
  [#n #k cases (leb k n) normalize // 
  |#o #v #Hind #k @eq_f lapply Hind -Hind elim v // 
   #hd #tl #Hind #Hind1 normalize @eq_f2 
    [@Hind1 %1 //|@Hind #x #Hx @Hind1 %2 //]
  ]
qed.

axiom lift_closed: ∀O,D.∀t:T O D.∀k,p. 
  is_closed O D 0 t → lift O D t k p = t.
(*
#O #D #t @(T_elim … t) normalize // 
  [#n #k normalize // 
  |#o #v #Hind #k @eq_f lapply Hind -Hind elim v // 
   #hd #tl #Hind #Hind1 normalize @eq_f2 
    [@Hind1 %1 //|@Hind #x #Hx @Hind1 %2 //]
  ]
qed. *)

let rec to_T O D ty on ty: FinSet_of_FType O D ty → T O D ≝ 
  match ty return (λty.FinSet_of_FType O D ty → T O D) with 
  [atom o ⇒ λa.Val O D o a
  |arrow ty1 ty2 ⇒ λa:FinFun ??.Vec O D ty1  
    (map ((FinSet_of_FType O D ty1)×(FinSet_of_FType O D ty2)) 
     (T O D) (λp.to_T O D ty2 (snd … p)) (pi1 … a))
  ]
.

axiom inj_to_T: ∀O,D,ty,a1,a2. to_T O D ty a1 = to_T O D ty a2 → a1 = a2.

let rec assoc (A:FinSet) (B:Type[0]) (a:A) l1 l2 on l1 : option B ≝
  match l1 with
  [ nil ⇒  None ?
  | cons hd1 tl1 ⇒ match l2 with
    [ nil ⇒ None ?
    | cons hd2 tl2 ⇒ if a==hd1 then Some ? hd2 else assoc A B a tl1 tl2
    ]
  ]. 
  
lemma same_assoc: ∀A,B,a,l1,v1,v2,N,N1.
  assoc A B a l1 (v1@N::v2) = Some ? N ∧ assoc A B a l1 (v1@N1::v2) = Some ? N1 
   ∨ assoc A B a l1 (v1@N::v2) = assoc A B a l1 (v1@N1::v2).
#A #B #a #l1 #v1 #v2 #N #N1 lapply v1 -v1 elim l1 
  [#v1 %2 // |#hd #tl #Hind * normalize cases (a==hd) normalize /3/]
qed.

lemma assoc_to_mem: ∀A,B,a,l1,l2,b. 
  assoc A B a l1 l2 = Some ? b → mem ? b l2.
#A #B #a #l1 elim l1
  [#l2 #b normalize #H destruct
  |#hd1 #tl1 #Hind * 
    [#b normalize #H destruct
    |#hd2 #tl2 #b normalize cases (a==hd1) normalize
      [#H %1 destruct //|#H %2 @Hind @H]
    ]
  ]
qed.

inductive red (O:Type[0]) (D:O→FinSet) : T O D  →T O D → Prop ≝
  | rbeta: ∀P,M,N. red O D (App O D (Lambda O D P M) N) (subst O D M 0 N)
  | riota: ∀ty,v,a,M. 
      assoc (FinSet_of_FType O D ty) ? a (enum (FinSet_of_FType O D ty)) v = Some ? M →
      red O D (App O D (Vec O D ty v) (to_T O D ty a)) M
  | rappl: ∀M,M1,N. red O D M M1 → red O D (App O D M N) (App O D M1 N)
  | rappr: ∀M,N,N1. red O D N N1 → red O D (App O D M N) (App O D M N1)
  | rmem: ∀ty,M. red O D (Lambda O D ty M)
      (Vec O D ty (map ?? (λa. subst O D M 0 (to_T O D ty a)) 
      (enum (FinSet_of_FType O D ty)))) 
  | rvec: ∀ty,N,N1,v,v1. red O D N N1 → 
      red O D (Vec O D ty (v@N::v1)) (Vec O D ty (v@N1::v1)).
 
(* some inversion cases *)
lemma red_vec: ∀O,D,ty,v,M.
  red O D (Vec O D ty v) M → ∃N,N1,v1,v2.
      red O D N N1 ∧ v = v1@N::v2 ∧ M = Vec O D ty (v1@N1::v2).
#O #D #ty #v #M #Hred inversion Hred
  [#ty1 #M0 #N #H destruct
  |#ty1 #v1 #a #M0 #_ #H destruct
  |#M0 #M1 #N #_ #_ #H destruct
  |#M0 #M1 #N #_ #_ #H destruct
  |#ty1 #M0 #H destruct
  |#ty1 #N #N1 #v1 #v2 #Hred1 #_ #H destruct #_ %{N} %{N1} %{v1} %{v2} /3/
  ]
qed.
      
lemma red_lambda: ∀O,D,ty,M,N.
  red O D (Lambda O D ty M) N → 
      N = Vec O D ty (map ?? (λa. subst O D M 0 (to_T O D ty a)) 
      (enum (FinSet_of_FType O D ty))).
#O #D #ty #M #N #Hred inversion Hred
  [#ty1 #M0 #N #H destruct
  |#ty1 #v1 #a #M0 #_ #H destruct
  |#M0 #M1 #N #_ #_ #H destruct
  |#M0 #M1 #N #_ #_ #H destruct
  |#ty1 #M0 #H destruct #_ //
  |#ty1 #N #N1 #v1 #v2 #Hred1 #_ #H destruct
  ]
qed. 

lemma red_val: ∀O,D,ty,a,N.
  red O D (Val O D ty a) N → False.
#O #D #ty #M #N #Hred inversion Hred
  [#ty1 #M0 #N #H destruct
  |#ty1 #v1 #a #M0 #_ #H destruct
  |#M0 #M1 #N #_ #_ #H destruct
  |#M0 #M1 #N #_ #_ #H destruct
  |#ty1 #M0 #H destruct #_ 
  |#ty1 #N #N1 #v1 #v2 #Hred1 #_ #H destruct
  ]
qed. 

lemma red_rel: ∀O,D,n,N.
  red O D (Rel O D n) N → False.
#O #D #n #N #Hred inversion Hred
  [#ty1 #M0 #N #H destruct
  |#ty1 #v1 #a #M0 #_ #H destruct
  |#M0 #M1 #N #_ #_ #H destruct
  |#M0 #M1 #N #_ #_ #H destruct
  |#ty1 #M0 #H destruct #_ 
  |#ty1 #N #N1 #v1 #v2 #Hred1 #_ #H destruct
  ]
qed. 
 
lemma star_red_appl: ∀O,D,M,M1,N. star ? (red O D) M M1 → 
  star ? (red O D) (App O D M N) (App O D M1 N).
#O #D #M #N #N1 #H elim H // 
#P #Q #Hind #HPQ #Happ %1[|@Happ] @rappl @HPQ
qed.

lemma star_red_appr: ∀O,D,M,N,N1. star ? (red O D) N N1 → 
  star ? (red O D) (App O D M N) (App O D M N1).
#O #D #M #N #N1 #H elim H // 
#P #Q #Hind #HPQ #Happ %1[|@Happ] @rappr @HPQ
qed.

lemma star_red_vec: ∀O,D,ty,N,N1,v1,v2. star ? (red O D) N N1 → 
  star ? (red O D) (Vec O D ty (v1@N::v2)) (Vec O D ty (v1@N1::v2)).
#O #D #ty #N #N1 #v1 #v2 #H elim H // 
#P #Q #Hind #HPQ #Hvec %1[|@Hvec] @rvec @HPQ
qed.

axiom red_subst : ∀O,D,M,N,N1,i. 
  red O D N N1 → red O D (subst O D M i N) (subst O D M i N1).
  
axiom red_star_subst : ∀O,D,M,N,N1,i. 
  star ? (red O D) N N1 → star ? (red O D) (subst O D M i N) (subst O D M i N1).

axiom canonical_to_T: ∀O,D.∀M:T O D.∀ty.(* type_of M ty → *)
  ∃a:FinSet_of_FType O D ty. star ? (red O D) M (to_T O D ty a).
   
axiom normal_to_T: ∀O,D,M,ty,a. red O D (to_T O D ty a) M → False.

lemma critical: ∀O,D,ty,M,N. 
  ∃M3:T O D
  .star (T O D) (red O D) (subst O D M 0 N) M3
   ∧star (T O D) (red O D)
    (App O D
     (Vec O D ty
      (map (FinSet_of_FType O D ty) (T O D)
       (λa0:FinSet_of_FType O D ty.subst O D M 0 (to_T O D ty a0))
       (enum (FinSet_of_FType O D ty)))) N) M3.
#O #D #ty #M #N
lapply (canonical_to_T O D N ty) * #a #Ha
%{(subst O D M 0 (to_T O D ty a))} (* CR-term *)
%[@red_star_subst @Ha
 |@trans_star [|@(star_red_appr … Ha)] @R_to_star @riota
  lapply (enum_complete (FinSet_of_FType O D ty) a)
  elim (enum (FinSet_of_FType O D ty))
   [normalize #H1 destruct (H1)
   |#hd #tl #Hind #H cases (orb_true_l … H) -H #Hcase
     [normalize >Hcase >(\P Hcase) //
     |normalize cases (true_or_false (a==hd)) #Hcase1
       [normalize >Hcase1 >(\P Hcase1) // |>Hcase1 @Hind @Hcase]
     ]
   ]
 ]
qed.

lemma critical2: ∀O,D,ty,a,M,M1,M2,v.
  red O D (Vec O D ty v) M →
  red O D (App O D (Vec O D ty v) (to_T O D ty a)) M1 →
  assoc (FinSet_of_FType O D ty) (T O D) a (enum (FinSet_of_FType O D ty)) v
    =Some (T O D) M2 →
  ∃M3:T O D
  .star (T O D) (red O D) M2 M3
   ∧star (T O D) (red O D) (App O D M (to_T O D ty a)) M3.
#O #D #ty #a #M #M1 #M2 #v #redM #redM1 #Ha lapply (red_vec … redM) -redM
* #N * #N1 * #v1 * #v2 * * #Hred1 #Hv #HM0 >HM0 -HM0 >Hv in Ha; #Ha
cases (same_assoc … a (enum (FinSet_of_FType O D ty)) v1 v2 N N1)
  [* >Ha -Ha #H1 destruct (H1) #Ha
   %{N1} (* CR-term *) % [@R_to_star //|@R_to_star @(riota … Ha)]
  |#Ha1 %{M2} (* CR-term *) % [// | @R_to_star @riota <Ha1 @Ha]
  ]
qed.

(* we need to proceed by structural induction on the term and then
by inversion on the two redexes. The problem are the moves in a 
same subterm, since we need an induction hypothesis, there *)

lemma local_confluence: ∀O,D,M,M1,M2. red O D M M1 → red O D M M2 → 
∃M3. star ? (red O D) M1 M3 ∧ star ? (red O D) M2 M3. 
#O #D #M @(T_elim … M)
  [#o #a #M1 #M2 #H elim(red_val ????? H)
  |#n #M1 #M2 #H elim(red_rel ???? H)
  |(* app : this is the interesting case *)
   #P #Q #HindP #HindQ
   #M1 #M2 #H1 inversion H1 -H1
    [(* right redex is beta *)
     #ty #Q #N #HM >HM -HM #HM1 >HM1 - HM1 #Hl inversion Hl
      [#P1 #M1 #N1 #H1 destruct (H1) #H_ %{(subst O D M1 0 N1)} (* CR-term *) /2/
      |#ty #v #a #M0 #_ #H1 destruct (H1) (* vacuous *)
      |#M0 #M10 #N0 #redM0 #_ #H1 destruct (H1) #_ inversion redM0
        [#P0 #M0 #N #H destruct
        |#ty #v #a #M0 #_ #H1 destruct (H1)
        |#M0 #M1 #N #_ #_ #H1 destruct (H1)
        |#M0 #M1 #N #_ #_ #H1 destruct (H1)
        |#ty1 #M0 #H1 destruct (H1) #HM1 @critical
        |#ty #N #N1 #v #v1 #_ #_ #H1 destruct (H1)
        ]
      |#M0 #N0 #N1 #redN0N1 #_ #H1 destruct (H1) #HM2
       %{(subst O D Q 0 N1)} (* CR-term *) 
       %[@red_star_subst @R_to_star //|@R_to_star @rbeta]
      |#ty1 #M0 #H1 destruct (H1) (* vacuous *)
      |#ty1 #N0 #N1 #v #v1 #_ #_ #H1 destruct (H1) (* vacuous *)
      ]
    |(* right redex is iota *)#ty #v #a #M3 #Ha #_ #_ #Hl inversion Hl
      [#P1 #M1 #N1 #H1 destruct (H1) (* vacuous *)
      |#ty1 #v1 #a1 #M4 #Ha1 #H1 destruct (H1) -H1 #HM4 >(inj_to_T … e0) in Ha;
       >Ha1 #H1 destruct (H1) %{M3} (* CR-term *) /2/
      |#M0 #M10 #N0 #redM0 #_ #H1 destruct (H1) #HM2 @(critical2 … redM0 Hl Ha)
      |#M0 #N0 #N1 #redN0N1 #_ #H1 destruct (H1) elim (normal_to_T … redN0N1)
      |#ty1 #M0 #H1 destruct (H1) (* vacuous *)
      |#ty1 #N0 #N1 #v #v1 #_ #_ #H1 destruct (H1) (* vacuous *)
      ]
    |(* right redex is appl *)#M3 #M4 #N #redM3M4 #_ #H1 destruct (H1) #_ 
      #Hl inversion Hl
      [#ty1 #M1 #N1 #H1 destruct (H1) #HM2 lapply (red_lambda … redM3M4)
       #H >H -H lapply (critical O D ty1 M1 N1) * #M3 * #H1 #H2 
       %{M3} /2/
      |#ty1 #v1 #a1 #M4 #Ha1 #H1 #H2 destruct 
       lapply (critical2 … redM3M4 Hl Ha1) * #M3 * #H1 #H2 %{M3} /2/
      |#M0 #M10 #N0 #redM0 #_ #H1 destruct (H1) #HM2 
       lapply (HindP … redM0 redM3M4) * #M3 * #H1 #H2 
       %{(App O D M3 N0)} (* CR-term *) % [@star_red_appl //|@star_red_appl //]
      |#M0 #N0 #N1 #redN0N1 #_ #H1 destruct (H1) #_
       %{(App O D M4 N1)} % @R_to_star [@rappr //|@rappl //]
      |#ty1 #M0 #H1 destruct (H1) (* vacuous *)
      |#ty1 #N0 #N1 #v #v1 #_ #_ #H1 destruct (H1) (* vacuous *)
      ]
    |(* right redex is appr *)#M3 #N #N1 #redN #_ #H1 destruct (H1) #_ 
      #Hl inversion Hl
      [#ty1 #M0 #N0 #H1 destruct (H1) #HM2 
       %{(subst O D M0 0 N1)} (* CR-term *) % 
        [@R_to_star @rbeta | @red_star_subst @R_to_star //]
      |#ty1 #v1 #a1 #M4 #Ha1 #H1 #H2 destruct (H1) elim (normal_to_T … redN)
      |#M0 #M10 #N0 #redM0 #_ #H1 destruct (H1) #HM2 
       %{(App O D M10 N1)} (* CR-term *) % @R_to_star [@rappl //|@rappr //]
      |#M0 #N0 #N10 #redN0 #_ #H1 destruct (H1) #_
       lapply (HindQ … redN0 redN) * #M3 * #H1 #H2 
       %{(App O D M0 M3)} (* CR-term *) % [@star_red_appr //|@star_red_appr //]
      |#ty1 #M0 #H1 destruct (H1) (* vacuous *)
      |#ty1 #N0 #N1 #v #v1 #_ #_ #H1 destruct (H1) (* vacuous *)
      ]
    |(* right redex is rmem *) #ty #M0 #H1 destruct (H1) (* vacuous *)
    |(* right redex is vec *) #ty #N #N1 #v #v1 #_ #_ 
     #H1 destruct (H1) (* vacuous *)
    ]
  |#ty #M1 #Hind #M2 #M3 #H1 #H2  
   lapply (red_lambda … H1) #HM2 lapply (red_lambda … H2) #HM3
   %{M2} (* CR-term *) % //
  |#ty #v1 #Hind #M1 #M2 #H1 #H2
   lapply (red_vec … H1) * #N11 * #N12 * #v11 * #v12 * * #redN11 #Hv1 #HM1
   lapply (red_vec … H2) * #N21* #N22 * #v21 * #v22 * * #redN21 #Hv2 #HM2
   >Hv1 in Hv2; #Hvv lapply (compare_append … Hvv) -Hvv * 
   (* we must proceed by cases on the list *) * normalize
    [(* N11 = N21 *) *
      [>append_nil * #Hl1 #Hl2 destruct lapply(Hind N11 … redN11 redN21)
        [@mem_append_l2 %1 //]
       * #M3 * #HM31 #HM32
       %{(Vec O D ty (v21@M3::v12))} (* CR-term *) 
       % [@star_red_vec //|@star_red_vec //]
      |>append_nil * #Hl1 #Hl2 destruct lapply(Hind N21 … redN21 redN11)
        [@mem_append_l2 %1 //]
       * #M3 * #HM31 #HM32
       %{(Vec O D ty (v11@M3::v22))} (* CR-term *) 
       % [@star_red_vec //|@star_red_vec //]
      ]
    |(* N11 ≠  N21 *) -Hind #P #l *
      [* #Hv11 #Hv22 destruct
       %{((Vec O D ty ((v21@N22::l)@N12::v12)))} (* CR-term *) % @R_to_star 
        [>associative_append >associative_append normalize @rvec //
        |>append_cons <associative_append <append_cons in ⊢ (???%?); @rvec //
        ]
      |* #Hv11 #Hv22 destruct
       %{((Vec O D ty ((v11@N12::l)@N22::v22)))} (* CR-term *) % @R_to_star 
        [>append_cons <associative_append <append_cons in ⊢ (???%?); @rvec //
        |>associative_append >associative_append normalize @rvec //
        ]
      ]
    ]
  ]
qed.    
      




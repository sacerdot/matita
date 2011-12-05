(**************************************************************************)
(*       ___                                                              *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||         The HELM team.                                      *)
(*      ||A||         http://helm.cs.unibo.it                             *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU General Public License Version 2                  *)
(*                                                                        *)
(**************************************************************************)

include "re/re.ma".

let rec move (S: Alpha) (x:S) (E: pitem S) on E : pre S ≝
 match E with
  [ pz ⇒ 〈 ∅, false 〉
  | pe ⇒ 〈 ϵ, false 〉
  | ps y ⇒ 〈 `y, false 〉
  | pp y ⇒ 〈 `y, x == y 〉
  | po e1 e2 ⇒ (move ? x e1) ⊕ (move ? x e2) 
  | pc e1 e2 ⇒ (move ? x e1) ⊙ (move ? x e2)
  | pk e ⇒ (move ? x e)^⊛ ].
  
lemma move_plus: ∀S:Alpha.∀x:S.∀i1,i2:pitem S.
  move S x (i1 + i2) = (move ? x i1) ⊕ (move ? x i2).
// qed.

lemma move_cat: ∀S:Alpha.∀x:S.∀i1,i2:pitem S.
  move S x (i1 · i2) = (move ? x i1) ⊙ (move ? x i2).
// qed.

lemma move_star: ∀S:Alpha.∀x:S.∀i:pitem S.
  move S x i^* = (move ? x i)^⊛.
// qed.

lemma fst_eq : ∀A,B.∀a:A.∀b:B. \fst 〈a,b〉 = a.
// qed.

lemma snd_eq : ∀A,B.∀a:A.∀b:B. \snd 〈a,b〉 = b.
// qed.

definition pmove ≝ λS:Alpha.λx:S.λe:pre S. move ? x (\fst e).

lemma pmove_def : ∀S:Alpha.∀x:S.∀i:pitem S.∀b. 
  pmove ? x 〈i,b〉 = move ? x i.
// qed.

lemma eq_to_eq_hd: ∀A.∀l1,l2:list A.∀a,b. 
  a::l1 = b::l2 → a = b.
#A #l1 #l2 #a #b #H destruct //
qed. 

axiom same_kernel: ∀S:Alpha.∀a:S.∀i:pitem S.
  |\fst (move ? a i)| = |i|.
(* #S #a #i elim i //
  [#i1 #i2 >move_cat
   cases (move S a i1) #i11 #b1 >fst_eq #IH1 
   cases (move S a i2) #i21 #b2 >fst_eq #IH2 
   normalize *)

axiom iff_trans:∀A,B,C. A ↔ B → B ↔ C → A ↔ C.
axiom iff_or_l: ∀A,B,C. A ↔ B → C ∨ A ↔ C ∨ B.
axiom iff_or_r: ∀A,B,C. A ↔ B → A ∨ C ↔ B ∨ C.

axiom epsilon_in_star: ∀S.∀A:word S → Prop. A^* [ ].

theorem move_ok:
 ∀S:Alpha.∀a:S.∀i:pitem S.∀w: word S. 
   \sem{move ? a i} w ↔ \sem{i} (a::w).
#S #a #i elim i 
  [normalize /2/
  |normalize /2/
  |normalize /2/
  |normalize #x #w cases (true_or_false (a==x)) #H >H normalize
    [>(proj1 … (eqb_true …) H) % 
      [* // #bot @False_ind //| #H1 destruct /2/]
    |% [#bot @False_ind // 
       | #H1 destruct @(absurd ((a==a)=true))
         [>(proj2 … (eqb_true …) (refl …)) // | /2/] 
       ]
    ]
  |#i1 #i2 #HI1 #HI2 #w >(sem_cat S i1 i2) >move_cat
   @iff_trans[|@sem_odot] >same_kernel >sem_cat_w
   @iff_trans[||@(iff_or_l … (HI2 w))] @iff_or_r %
    [* #w1 * #w2 * * #eqw #w1in #w2in @(ex_intro … (a::w1))
     @(ex_intro … w2) % // % normalize // cases (HI1 w1) /2/
    |* #w1 * #w2 * cases w1
      [* #_ #H @False_ind /2/
      |#x #w3 * #eqaw normalize in eqaw; destruct #w3in #w2in 
      @(ex_intro … w3) @(ex_intro … w2) % // % // cases (HI1 w3) /2/
      ]
    ]
  |#i1 #i2 #HI1 #HI2 #w >(sem_plus S i1 i2) >move_plus >sem_plus_w 
   @iff_trans[|@sem_oplus] 
   @iff_trans[|@iff_or_l [|@HI2]| @iff_or_r //]
  |#i1 #HI1 #w >move_star 
   @iff_trans[|@sem_ostar] >same_kernel >sem_star_w %
    [* #w1 * #w2 * * #eqw #w1in #w2in 
     @(ex_intro … (a::w1)) @(ex_intro … w2) % // % normalize //
     cases (HI1 w1 ) /2/
    |* #w1 * #w2 * cases w1
      [* #_ #H @False_ind /2/
      |#x #w3 * #eqaw normalize in eqaw; destruct #w3in #w2in 
       @(ex_intro … w3) @(ex_intro … w2) % // % // cases (HI1 w3) /2/
      ]
    ]
  ]
qed.
    
notation > "x ↦* E" non associative with precedence 60 for @{moves ? $x $E}.
let rec moves (S : Alpha) w e on w : pre S ≝
 match w with
  [ nil ⇒ e
  | cons x w' ⇒ w' ↦* (move S x (\fst e))].

lemma moves_empty: ∀S:Alpha.∀e:pre S. 
  moves ? [ ] e = e.
// qed.

lemma moves_cons: ∀S:Alpha.∀a:S.∀w.∀e:pre S. 
  moves ? (a::w)  e = moves ? w (move S a (\fst e)).
// qed.

lemma not_epsilon_sem: ∀S:Alpha.∀a:S.∀w: word S. ∀e:pre S. 
  iff ((a::w) ∈ e) ((a::w) ∈ \fst e).
#S #a #w * #i #b >fst_eq cases b normalize 
  [% /2/ * // #H destruct |% normalize /2/]
qed.

lemma same_kernel_moves: ∀S:Alpha.∀w.∀e:pre S.
  |\fst (moves ? w e)| = |\fst e|.
#S #w elim w //
qed.

axiom iff_not: ∀A,B. (iff A B) →(iff (¬A) (¬B)).

axiom iff_sym: ∀A,B. (iff A B) →(iff B A).
    
theorem decidable_sem: ∀S:Alpha.∀w: word S. ∀e:pre S. 
   (\snd (moves ? w e) = true)  ↔ \sem{e} w.
#S #w elim w 
 [* #i #b >moves_empty cases b % /2/
 |#a #w1 #Hind #e >moves_cons
  @iff_trans [||@iff_sym @not_epsilon_sem]
  @iff_trans [||@move_ok] @Hind
 ]
qed.

lemma not_true_to_false: ∀b.b≠true → b =false.
#b * cases b // #H @False_ind /2/ 
qed. 

theorem equiv_sem: ∀S:Alpha.∀e1,e2:pre S. 
  iff (\sem{e1} =1 \sem{e2}) (∀w.\snd (moves ? w e1) = \snd (moves ? w e2)).
#S #e1 #e2 % 
[#same_sem #w 
  cut (∀b1,b2. iff (b1 = true) (b2 = true) → (b1 = b2)) 
    [* * // * #H1 #H2 [@sym_eq @H1 //| @H2 //]]
  #Hcut @Hcut @iff_trans [|@decidable_sem] 
  @iff_trans [|@same_sem] @iff_sym @decidable_sem
|#H #w1 @iff_trans [||@decidable_sem] <H @iff_sym @decidable_sem]
qed.

axiom moves_left : ∀S,a,w,e. 
  moves S (w@[a]) e = move S a (\fst (moves S w e)). 

definition in_moves ≝ λS:Alpha.λw.λe:pre S. \snd(w ↦* e).

coinductive equiv (S:Alpha) : pre S → pre S → Prop ≝
 mk_equiv:
  ∀e1,e2: pre S.
   \snd e1  = \snd e2 →
    (∀x. equiv S (move ? x (\fst e1)) (move ? x (\fst e2))) →
     equiv S e1 e2.

definition beqb ≝ λb1,b2.
  match b1 with
  [ true ⇒ b2
  | false ⇒ notb b2
  ].

lemma beqb_ok: ∀b1,b2. iff (beqb b1 b2 = true) (b1 = b2).
#b1 #b2 cases b1 cases b2 normalize /2/
qed.

definition Bin ≝ mk_Alpha bool beqb beqb_ok. 

let rec beqitem S (i1,i2: pitem S) on i1 ≝ 
  match i1 with
  [ pz ⇒ match i2 with [ pz ⇒ true | _ ⇒ false]
  | pe ⇒ match i2 with [ pe ⇒ true | _ ⇒ false]
  | ps y1 ⇒ match i2 with [ ps y2 ⇒ y1==y2 | _ ⇒ false]
  | pp y1 ⇒ match i2 with [ pp y2 ⇒ y1==y2 | _ ⇒ false]
  | po i11 i12 ⇒ match i2 with 
    [ po i21 i22 ⇒ beqitem S i11 i21 ∧ beqitem S i12 i22
    | _ ⇒ false]
  | pc i11 i12 ⇒ match i2 with 
    [ pc i21 i22 ⇒ beqitem S i11 i21 ∧ beqitem S i12 i22
    | _ ⇒ false]
  | pk i11 ⇒ match i2 with [ pk i21 ⇒ beqitem S i11 i21 | _ ⇒ false]
  ].

axiom beqitem_ok: ∀S,i1,i2. iff (beqitem S i1 i2 = true) (i1 = i2). 

definition BinItem ≝ 
  mk_Alpha (pitem Bin) (beqitem Bin) (beqitem_ok Bin).

definition beqpre ≝ λS:Alpha.λe1,e2:pre S. 
  beqitem S (\fst e1) (\fst e2) ∧ beqb (\snd e1) (\snd e2).
  
definition beqpairs ≝ λS:Alpha.λp1,p2:(pre S)×(pre S). 
  beqpre S (\fst p1) (\fst p2) ∧ beqpre S (\snd p1) (\snd p2).
  
axiom beqpairs_ok: ∀S,p1,p2. iff (beqpairs S p1 p2 = true) (p1 = p2). 

definition space ≝ λS.mk_Alpha ((pre S)×(pre S)) (beqpairs S) (beqpairs_ok S).

let rec memb (S:Alpha) (x:S) (l: list S) on l  ≝
  match l with
  [ nil ⇒ false
  | cons a tl ⇒ (a == x) || memb S x tl
  ].
  
lemma memb_hd: ∀S,a,l. memb S a (a::l) = true.
#S #a #l normalize >(proj2 … (eqb_true S …) (refl S a)) //
qed.

lemma memb_cons: ∀S,a,b,l. 
  memb S a l = true → memb S a (b::l) = true.
#S #a #b #l normalize cases (b==a) normalize // 
qed.

lemma memb_append: ∀S,a,l1,l2. 
memb S a (l1@l2) = true →
  memb S a l1= true ∨ memb S a l2 = true.
#S #a #l1 elim l1 normalize [/2/] #b #tl #Hind
#l2 cases (b==a) normalize /2/ 
qed. 

lemma memb_append_l1: ∀S,a,l1,l2. 
 memb S a l1= true → memb S a (l1@l2) = true.
#S #a #l1 elim l1 normalize
  [normalize #le #abs @False_ind /2/
  |#b #tl #Hind #l2 cases (b==a) normalize /2/ 
  ]
qed. 

lemma memb_append_l2: ∀S,a,l1,l2. 
 memb S a l2= true → memb S a (l1@l2) = true.
#S #a #l1 elim l1 normalize //
#b #tl #Hind #l2 cases (b==a) normalize /2/ 
qed. 

let rec uniqueb (S:Alpha) l on l : bool ≝
  match l with 
  [ nil ⇒ true
  | cons a tl ⇒ notb (memb S a tl) ∧ uniqueb S tl
  ].

definition sons ≝ λp:space Bin. 
  [〈move Bin true (\fst (\fst p)), move Bin true (\fst (\snd p))〉;
   〈move Bin false (\fst (\fst p)), move Bin false (\fst (\snd p))〉
  ].

axiom memb_sons: ∀p,q. memb (space Bin) p (sons q) = true →
  ∃a.(move ? a (\fst (\fst q)) = \fst p ∧
      move ? a (\fst (\snd q)) = \snd p).

(*
let rec test_sons (l:list (space Bin)) ≝ 
  match l with 
  [ nil ⇒  true
  | cons hd tl ⇒ 
    beqb (\snd (\fst hd)) (\snd (\snd hd)) ∧ test_sons tl
  ]. *)

let rec unique_append (S:Alpha) (l1,l2: list S) on l1 ≝
  match l1 with
  [ nil ⇒ l2
  | cons a tl ⇒ 
     let r ≝ unique_append S tl l2 in
     if (memb S a r) then r else a::r
  ].

lemma unique_append_unique: ∀S,l1,l2. uniqueb S l2 = true →
  uniqueb S (unique_append S l1 l2) = true.
#S #l1 elim l1 normalize // #a #tl #Hind #l2 #uniquel2
cases (true_or_false … (memb S a (unique_append S tl l2))) 
#H >H normalize [@Hind //] >H normalize @Hind //
qed.

let rec bisim (n:nat) (frontier,visited: list (space Bin)) ≝
  match n with 
  [ O ⇒ 〈false,visited〉 (* assert false *)
  | S m ⇒ 
    match frontier with
    [ nil ⇒ 〈true,visited〉
    | cons hd tl ⇒
      if beqb (\snd (\fst hd)) (\snd (\snd hd)) then
        bisim m (unique_append ? (filter ? (λx.notb (memb ? x (hd::visited))) 
        (sons hd)) tl) (hd::visited)
      else 〈false,visited〉
    ]
  ].
  
lemma unfold_bisim: ∀n.∀frontier,visited: list (space Bin).
  bisim n frontier visited =
  match n with 
  [ O ⇒ 〈false,visited〉 (* assert false *)
  | S m ⇒ 
    match frontier with
    [ nil ⇒ 〈true,visited〉
    | cons hd tl ⇒
      if beqb (\snd (\fst hd)) (\snd (\snd hd)) then
        bisim m (unique_append ? (filter ? (λx.notb(memb ? x (hd::visited))) (sons hd)) tl) (hd::visited)
      else 〈false,visited〉
    ]
  ].
#n cases n // qed.
  
lemma bisim_never: ∀frontier,visited: list (space Bin).
  bisim O frontier visited = 〈false,visited〉.
#frontier #visited >unfold_bisim // 
qed.

lemma bisim_end: ∀m.∀visited: list (space Bin).
  bisim (S m) [] visited = 〈true,visited〉.
#n #visisted >unfold_bisim // 
qed.

lemma bisim_step_true: ∀m.∀p.∀frontier,visited: list (space Bin).
beqb (\snd (\fst p)) (\snd (\snd p)) = true →
  bisim (S m) (p::frontier) visited = 
  bisim m (unique_append ? (filter ? (λx.notb(memb (space Bin) x (p::visited))) (sons p)) frontier) (p::visited).
#m #p #frontier #visited #test >unfold_bisim normalize nodelta >test // 
qed.

lemma bisim_step_false: ∀m.∀p.∀frontier,visited: list (space Bin).
beqb (\snd (\fst p)) (\snd (\snd p)) = false →
  bisim (S m) (p::frontier) visited = 〈false,visited〉.
#m #p #frontier #visited #test >unfold_bisim normalize nodelta >test // 
qed.
 
definition visited_inv ≝ λe1,e2:pre Bin.λvisited: list (space Bin).
uniqueb ? visited = true ∧  
  ∀p. memb ? p visited = true → 
   (∃w.(moves Bin w e1 = \fst p) ∧ (moves Bin w e2 = \snd p)) ∧ 
   (beqb (\snd (\fst p)) (\snd (\snd p)) = true).
  
definition frontier_inv ≝ λfrontier,visited: list (space Bin).
uniqueb ? frontier = true ∧ 
∀p. memb ? p frontier = true →  
  memb ? p visited = false ∧
  ∃p1.((memb ? p1 visited = true) ∧
   (∃a. move ? a (\fst (\fst p1)) = \fst p ∧ 
        move ? a (\fst (\snd p1)) = \snd p)).

definition orb_true_r1: ∀b1,b2:bool. 
  b1 = true → (b1 ∨ b2) = true.
#b1 #b2 #H >H // qed.

definition orb_true_r2: ∀b1,b2:bool. 
  b2 = true → (b1 ∨ b2) = true.
#b1 #b2 #H >H cases b1 // qed.

definition orb_true_l: ∀b1,b2:bool. 
  (b1 ∨ b2) = true → (b1 = true) ∨ (b2 = true).
* normalize /2/ qed.

definition andb_true_l1: ∀b1,b2:bool. 
  (b1 ∧ b2) = true → (b1 = true).
#b1 #b2 cases b1 normalize //.
qed.

definition andb_true_l2: ∀b1,b2:bool. 
  (b1 ∧ b2) = true → (b2 = true).
#b1 #b2 cases b1 cases b2 normalize //.
qed.

definition andb_true_l: ∀b1,b2:bool. 
  (b1 ∧ b2) = true → (b1 = true) ∧ (b2 = true).
#b1 #b2 cases b1 normalize #H [>H /2/ |@False_ind /2/].
qed.

definition andb_true_r: ∀b1,b2:bool. 
  (b1 = true) ∧ (b2 = true) → (b1 ∧ b2) = true.
#b1 #b2 cases b1 normalize * // 
qed.

lemma notb_eq_true_l: ∀b. notb b = true → b = false.
#b cases b normalize //
qed.

lemma notb_eq_true_r: ∀b. b = false → notb b = true.
#b cases b normalize //
qed.
 
lemma notb_eq_false_l:∀b. notb b = false → b = true.
#b cases b normalize //
qed.

lemma notb_eq_false_r:∀b. b = true → notb b = false.
#b cases b normalize //
qed.


axiom filter_true: ∀S,f,a,l. 
  memb S a (filter S f l) = true → f a = true.
(*
#S #f #a #l elim l [normalize #H @False_ind /2/]
#b #tl #Hind normalize cases (f b) normalize *)

axiom memb_filter_memb: ∀S,f,a,l. 
  memb S a (filter S f l) = true → memb S a l = true.
  
axiom unique_append_elim: ∀S:Alpha.∀P: S → Prop.∀l1,l2. 
(∀x. memb S x l1 = true → P x) → (∀x. memb S x l2 = true → P x) →
∀x. memb S x (unique_append S l1 l2) = true → P x. 

axiom not_memb_to_not_eq: ∀S,a,b,l. 
 memb S a l = false → memb S b l = true → a==b = false.

include "arithmetics/exp.ma".

let rec pos S (i:re S) on i ≝ 
  match i with
  [ z ⇒ 0
  | e ⇒ 0
  | s y ⇒ 1
  | o i1 i2 ⇒ pos S i1 + pos S i2
  | c i1 i2 ⇒ pos S i1 + pos S i2
  | k i ⇒ pos S i
  ].

definition sublist ≝ 
  λS,l1,l2.∀a. memb S a l1 = true → memb S a l2 = true.

lemma memb_exists: ∀S,a,l.memb S a l = true → 
  ∃l1,l2.l=l1@(a::l2).
#S #a #l elim l [normalize #abs @False_ind /2/]
#b #tl #Hind #H cases (orb_true_l … H)
  [#eqba @(ex_intro … (nil S)) @(ex_intro … tl)
   >(proj1 … (eqb_true …) eqba) //
  |#mem_tl cases (Hind mem_tl) #l1 * #l2 #eqtl
   @(ex_intro … (b::l1)) @(ex_intro … l2) >eqtl //
  ]
qed.

lemma length_append: ∀A.∀l1,l2:list A. 
  |l1@l2| = |l1|+|l2|.
#A #l1 elim l1 // normalize /2/
qed.

lemma sublist_length: ∀S,l1,l2. 
 uniqueb S l1 = true → sublist S l1 l2 → |l1| ≤ |l2|.
#S #l1 elim l1 // 
#a #tl #Hind #l2 #unique #sub
cut (∃l3,l4.l2=l3@(a::l4)) [@memb_exists @sub //]
* #l3 * #l4 #eql2 >eql2 >length_append normalize 
applyS le_S_S <length_append @Hind [@(andb_true_l2 … unique)]
>eql2 in sub; #sub #x #membx 
cases (memb_append … (sub x (orb_true_r2 … membx)))
  [#membxl3 @memb_append_l1 //
  |#membxal4 cases (orb_true_l … membxal4)
    [#eqax @False_ind cases (andb_true_l … unique)
     >(proj1 … (eqb_true …) eqax) >membx normalize /2/
    |#membxl4 @memb_append_l2 //
    ]
  ]
qed.

axiom memb_filter: ∀S,f,l,x. memb S x (filter ? f l) = true → 
memb S x l = true ∧ (f x = true).

axiom memb_filter_l: ∀S,f,l,x. memb S x l = true → (f x = true) →
memb S x (filter ? f l) = true.

axiom sublist_unique_append_l1: 
  ∀S,l1,l2. sublist S l1 (unique_append S l1 l2).
  
axiom sublist_unique_append_l2: 
  ∀S,l1,l2. sublist S l2 (unique_append S l1 l2).

definition compose ≝ λA,B,C.λf:A→B→C.λl1,l2.
    foldr ?? (λi,acc.(map ?? (f i) l2)@acc) [ ] l1.
  
let rec pitem_enum S (i:re S) on i ≝
  match i with
  [ z ⇒ [pz S]
  | e ⇒ [pe S]
  | s y ⇒ [ps S y; pp S y]
  | o i1 i2 ⇒ compose ??? (po S) (pitem_enum S i1) (pitem_enum S i2)
  | c i1 i2 ⇒ compose ??? (pc S) (pitem_enum S i1) (pitem_enum S i2)
  | k i ⇒ map ?? (pk S) (pitem_enum S i)
  ].

axiom memb_compose: ∀S1,S2,S3,op,a1,a2,l1,l2.   
  memb S1 a1 l1 = true → memb S2 a2 l2 = true →
  memb S3 (op a1 a2) (compose S1 S2 S3 op l1 l2) = true.
(* #S #op #a1 #a2 #l1 elim l1 [normalize //]
#x #tl #Hind #l2 elim l2 [#_ normalize #abs @False_ind /2/]
#y #tl2 #Hind2 #membx #memby normalize *)

axiom pitem_enum_complete: ∀i: pitem Bin.
  memb BinItem i (pitem_enum ? (forget ? i)) = true.
(*
#i elim i
  [//
  |//
  |* //
  |* // 
  |#i1 #i2 #Hind1 #Hind2 @memb_compose //
  |#i1 #i2 #Hind1 #Hind2 @memb_compose //
  |
*)

definition pre_enum ≝ λS.λi:re S.
  compose ??? (λi,b.〈i,b〉) (pitem_enum S i) [true;false].
 
definition space_enum ≝ λS.λi1,i2:re S.
  compose ??? (λe1,e2.〈e1,e2〉) (pre_enum S i1) (pre_enum S i1).

axiom space_enum_complete : ∀S.∀e1,e2: pre S.
  memb (space S) 〈e1,e2〉 (space_enum S (|\fst e1|) (|\fst e2|)) = true.
   
lemma bisim_ok1: ∀e1,e2:pre Bin.\sem{e1}=1\sem{e2} → 
 ∀n.∀frontier,visited:list (space Bin).
 |space_enum Bin (|\fst e1|) (|\fst e2|)| < n + |visited|→
 visited_inv e1 e2 visited →  frontier_inv frontier visited →
 \fst (bisim n frontier visited) = true.
#e1 #e2 #same #n elim n 
  [#frontier #visited #abs * #unique #H @False_ind @(absurd … abs)
   @le_to_not_lt @sublist_length // * #e11 #e21 #membp 
   cut ((|\fst e11| = |\fst e1|) ∧ (|\fst e21| = |\fst e2|))
   [|* #H1 #H2 <H1 <H2 @space_enum_complete]
   cases (H … membp) * #w * >fst_eq >snd_eq #we1 #we2 #_
   <we1 <we2 % //    
  |#m #HI * [#visited #vinv #finv >bisim_end //]
   #p #front_tl #visited #Hn * #u_visited #vinv * #u_frontier #finv
   cases (finv p (memb_hd …)) #Hp * #p2 * #visited_p2
   * #a * #movea1 #movea2 
   cut (∃w.(moves Bin w e1 = \fst p) ∧ (moves Bin w e2 = \snd p))
     [cases (vinv … visited_p2) -vinv * #w1 * #mw1 #mw2 #_
      @(ex_intro … (w1@[a])) /2/] 
   -movea2 -movea1 -a -visited_p2 -p2 #reachp
   cut (beqb (\snd (\fst p)) (\snd (\snd p)) = true)
     [cases reachp #w * #move_e1 #move_e2 <move_e1 <move_e2
      @(proj2 … (beqb_ok … )) @(proj1 … (equiv_sem … )) @same 
     |#ptest >(bisim_step_true … ptest) @HI -HI
       [<plus_n_Sm //
       |% [@andb_true_r % [@notb_eq_false_l // | // ]]
        #p1 #H (cases (orb_true_l … H))
         [#eqp <(proj1 … (eqb_true (space Bin) ? p1) eqp) % // 
         |#visited_p1 @(vinv … visited_p1)
         ]
       |whd % [@unique_append_unique @(andb_true_l2 … u_frontier)]
        @unique_append_elim #q #H
         [% 
           [@notb_eq_true_l @(filter_true … H) 
           |@(ex_intro … p) % // 
            @(memb_sons … (memb_filter_memb … H))
           ]
         |cases (finv q ?) [|@memb_cons //]
          #nvq * #p1 * #Hp1 #reach %
           [cut ((p==q) = false) [|#Hpq whd in ⊢ (??%?); >Hpq @nvq]
            cases (andb_true_l … u_frontier) #notp #_ 
            @(not_memb_to_not_eq … H) @notb_eq_true_l @notp 
           |cases (proj2 … (finv q ?)) 
             [#p1 *  #Hp1 #reach @(ex_intro … p1) % // @memb_cons //
             |@memb_cons //
             ]
          ]
        ]  
      ]
    ]
  ]
qed.

definition all_true ≝ λl.∀p. memb (space Bin) p l = true → 
  (beqb (\snd (\fst p)) (\snd (\snd p)) = true).

definition sub_sons ≝ λl1,l2.∀x,a. 
memb (space Bin) x l1 = true → 
  memb (space Bin) 〈move ? a (\fst (\fst x)), move ? a (\fst (\snd x))〉 l2 = true.

lemma reachable_bisim: 
 ∀n.∀frontier,visited,visited_res:list (space Bin).
 all_true visited →
 sub_sons visited (frontier@visited) →
 bisim n frontier visited = 〈true,visited_res〉 → 
  (sub_sons visited_res visited_res ∧ 
   sublist ? visited visited_res ∧
   all_true visited_res).
#n elim n
  [#fron #vis #vis_res #_ #_ >bisim_never #H destruct
  |#m #Hind * 
    [-Hind #vis #vis_res #allv #H normalize in  ⊢ (%→?);
     #H1 destruct % // % // #p /2/ 
    |#hd cases (true_or_false (beqb (\snd (\fst hd)) (\snd (\snd hd))))
      [|#H #tl #vis #vis_res #allv >(bisim_step_false … H) #_ #H1 destruct]
     #H #tl #visited #visited_res #allv >(bisim_step_true … H)
     cut (all_true (hd::visited)) 
      [#p #H cases (orb_true_l … H) 
        [#eqp <(proj1 … (eqb_true …) eqp) // |@allv]]
     #allh #subH #bisim cases (Hind … allh … bisim) -Hind
      [* #H1 #H2 #H3 % // % // #p #H4 @H2 @memb_cons //]  
     #x #a #membx
     cases (orb_true_l … membx)
      [#eqhdx >(proj1 … (eqb_true …) eqhdx)
       letin xa ≝ 〈move Bin a (\fst (\fst x)), move Bin a (\fst (\snd x))〉
       cases (true_or_false … (memb (space Bin) xa (x::visited)))
        [#membxa @memb_append_l2 //
        |#membxa @memb_append_l1 @sublist_unique_append_l1 @memb_filter_l
          [whd in ⊢ (??(??%%)?); cases a [@memb_hd |@memb_cons @memb_hd]
          |>membxa //
          ]
        ]
      |#H1 letin xa ≝ 〈move Bin a (\fst (\fst x)), move Bin a (\fst (\snd x))〉
       cases (memb_append … (subH x a H1))  
        [#H2 (cases (orb_true_l … H2)) 
          [#H3 @memb_append_l2 >(proj1 … (eqb_true …) H3) @memb_hd
          |#H3 @memb_append_l1 @sublist_unique_append_l2 @H3
          ]
        |#H2 @memb_append_l2 @memb_cons @H2
        ]
      ]
    ]
  ]
qed.       

axiom bisim_char: ∀e1,e2:pre Bin.
(∀w.(beqb (\snd (moves ? w e1)) (\snd (moves ? w e2))) = true) → 
\sem{e1}=1\sem{e2}.

lemma bisim_ok2: ∀e1,e2:pre Bin.
 (beqb (\snd e1) (\snd e2) = true) →
 ∀n.∀frontier:list (space Bin).
 sub_sons [〈e1,e2〉] (frontier@[〈e1,e2〉]) →
 \fst (bisim n frontier [〈e1,e2〉]) = true → \sem{e1}=1\sem{e2}.
#e1 #e2 #Hnil #n #frontier #init #bisim_true
letin visited_res ≝ (\snd (bisim n frontier [〈e1,e2〉]))
cut (bisim n frontier [〈e1,e2〉] = 〈true,visited_res〉)
  [<bisim_true <eq_pair_fst_snd //] #H
cut (all_true [〈e1,e2〉]) 
  [#p #Hp cases (orb_true_l … Hp) 
    [#eqp <(proj1 … (eqb_true …) eqp) // 
    | whd in ⊢ ((??%?)→?); #abs @False_ind /2/
    ]] #allH 
cases (reachable_bisim … allH init … H) * #H1 #H2 #H3
cut (∀w,p.memb (space Bin) p visited_res = true → 
  memb (space Bin) 〈moves ? w (\fst p), moves ? w (\snd p)〉 visited_res = true)
  [#w elim w [* //] 
   #a #w1 #Hind * #e11 #e21 #visp >fst_eq >snd_eq >moves_cons >moves_cons 
   @(Hind 〈?,?〉) @(H1 〈?,?〉) //] #all_reach
@bisim_char #w @(H3 〈?,?〉) @(all_reach w 〈?,?〉) @H2 //
qed.
  
definition tt ≝ ps Bin true.
definition ff ≝ ps Bin false.
definition eps ≝ pe Bin.
definition exp1 ≝ (ff + tt · ff).
definition exp2 ≝  ff · (eps + tt).

definition exp3 ≝ move Bin true (\fst (•exp1)).
definition exp4 ≝ move Bin true (\fst (•exp2)).
definition exp5 ≝ move Bin false (\fst (•exp1)).
definition exp6 ≝ move Bin false (\fst (•exp2)).

example comp1 : bequiv 15 (•exp1) (•exp2) [ ] = false .
normalize //
qed.



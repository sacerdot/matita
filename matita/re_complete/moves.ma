include "re.ma".
include "basics/listb.ma".

let rec move (S: DeqSet) (x:S) (E: pitem S) on E : pre S ≝
 match E with
  [ pz ⇒ 〈 `∅, false 〉
  | pe ⇒ 〈 ϵ, false 〉
  | ps y ⇒ 〈 `y, false 〉
  | pp y ⇒ 〈 `y, x == y 〉
  | po e1 e2 ⇒ (move ? x e1) ⊕ (move ? x e2) 
  | pc e1 e2 ⇒ (move ? x e1) ⊙ (move ? x e2)
  | pk e ⇒ (move ? x e)^⊛ ].
  
lemma move_plus: ∀S:DeqSet.∀x:S.∀i1,i2:pitem S.
  move S x (i1 + i2) = (move ? x i1) ⊕ (move ? x i2).
// qed.

lemma move_cat: ∀S:DeqSet.∀x:S.∀i1,i2:pitem S.
  move S x (i1 · i2) = (move ? x i1) ⊙ (move ? x i2).
// qed.

lemma move_star: ∀S:DeqSet.∀x:S.∀i:pitem S.
  move S x i^* = (move ? x i)^⊛.
// qed.

definition pmove ≝ λS:DeqSet.λx:S.λe:pre S. move ? x (\fst e).

lemma pmove_def : ∀S:DeqSet.∀x:S.∀i:pitem S.∀b. 
  pmove ? x 〈i,b〉 = move ? x i.
// qed.

lemma eq_to_eq_hd: ∀A.∀l1,l2:list A.∀a,b. 
  a::l1 = b::l2 → a = b.
#A #l1 #l2 #a #b #H destruct //
qed. 

lemma same_kernel: ∀S:DeqSet.∀a:S.∀i:pitem S.
  |\fst (move ? a i)| = |i|.
#S #a #i elim i //
  [#i1 #i2 #H1 #H2 >move_cat >erase_odot //
  |#i1 #i2 #H1 #H2 >move_plus whd in ⊢ (??%%); // 
  ]
qed.

theorem move_ok:
 ∀S:DeqSet.∀a:S.∀i:pitem S.∀w: word S. 
   \sem{move ? a i} w ↔ \sem{i} (a::w).
#S #a #i elim i 
  [normalize /2/
  |normalize /2/
  |normalize /2/
  |normalize #x #w cases (true_or_false (a==x)) #H >H normalize
    [>(\P H) % [* // #bot @False_ind //| #H1 destruct /2/]
    |% [@False_ind |#H1 cases (\Pf H) #H2 @H2 destruct //]
    ]
  |#i1 #i2 #HI1 #HI2 #w >move_cat
   @iff_trans[|@sem_odot] >same_kernel >sem_cat_w
   @iff_trans[||@(iff_or_l … (HI2 w))] @iff_or_r 
   @iff_trans[||@iff_sym @deriv_middot //]
   @cat_ext_l @HI1
  |#i1 #i2 #HI1 #HI2 #w >(sem_plus S i1 i2) >move_plus >sem_plus_w 
   @iff_trans[|@sem_oplus] 
   @iff_trans[|@iff_or_l [|@HI2]| @iff_or_r //]
  |#i1 #HI1 #w >move_star 
   @iff_trans[|@sem_ostar] >same_kernel >sem_star_w 
   @iff_trans[||@iff_sym @deriv_middot //]
   @cat_ext_l @HI1
  ]
qed.
    
notation > "x ↦* E" non associative with precedence 65 for @{moves ? $x $E}.
let rec moves (S : DeqSet) w e on w : pre S ≝
 match w with
  [ nil ⇒ e
  | cons x w' ⇒ w' ↦* (move S x (\fst e))]. 

lemma moves_empty: ∀S:DeqSet.∀e:pre S. 
  moves ? [ ] e = e.
// qed.

lemma moves_cons: ∀S:DeqSet.∀a:S.∀w.∀e:pre S. 
  moves ? (a::w)  e = moves ? w (move S a (\fst e)).
// qed.

lemma moves_left : ∀S,a,w,e. 
  moves S (w@[a]) e = move S a (\fst (moves S w e)). 
#S #a #w elim w // #x #tl #Hind #e >moves_cons >moves_cons //
qed.

lemma not_epsilon_sem: ∀S:DeqSet.∀a:S.∀w: word S. ∀e:pre S. 
  iff ((a::w) ∈ e) ((a::w) ∈ \fst e).
#S #a #w * #i #b cases b normalize 
  [% /2/ * // #H destruct |% normalize /2/]
qed.

lemma same_kernel_moves: ∀S:DeqSet.∀w.∀e:pre S.
  |\fst (moves ? w e)| = |\fst e|.
#S #w elim w //
qed.

theorem decidable_sem: ∀S:DeqSet.∀w: word S. ∀e:pre S. 
   (\snd (moves ? w e) = true) ↔ \sem{e} w.
#S #w elim w 
 [* #i #b >moves_empty cases b % /2/
 |#a #w1 #Hind #e >moves_cons
  @iff_trans [||@iff_sym @not_epsilon_sem]
  @iff_trans [||@move_ok] @Hind
 ]
qed.

(************************ pit state ***************************)
definition pit_pre ≝ λS.λi.〈blank S (|i|), false〉. 

let rec occur (S: DeqSet) (i: re S) on i ≝  
  match i with
  [ z ⇒ [ ]
  | e ⇒ [ ]
  | s y ⇒ [y]
  | o e1 e2 ⇒ unique_append ? (occur S e1) (occur S e2) 
  | c e1 e2 ⇒ unique_append ? (occur S e1) (occur S e2) 
  | k e ⇒ occur S e].

lemma not_occur_to_pit: ∀S,a.∀i:pitem S. memb S a (occur S (|i|)) ≠ true →
  move S a i  = pit_pre S i.
#S #a #i elim i //
  [#x normalize cases (a==x) normalize // #H @False_ind /2/
  |#i1 #i2 #Hind1 #Hind2 #H >move_cat 
   >Hind1 [2:@(not_to_not … H) #H1 @sublist_unique_append_l1 //]
   >Hind2 [2:@(not_to_not … H) #H1 @sublist_unique_append_l2 //] //
  |#i1 #i2 #Hind1 #Hind2 #H >move_plus 
   >Hind1 [2:@(not_to_not … H) #H1 @sublist_unique_append_l1 //]
   >Hind2 [2:@(not_to_not … H) #H1 @sublist_unique_append_l2 //] //
  |#i #Hind #H >move_star >Hind // 
  ]
qed.

lemma move_pit: ∀S,a,i. move S a (\fst (pit_pre S i)) = pit_pre S i.
#S #a #i elim i //
  [#i1 #i2 #Hind1 #Hind2 >move_cat >Hind1 >Hind2 // 
  |#i1 #i2 #Hind1 #Hind2 >move_plus >Hind1 >Hind2 // 
  |#i #Hind >move_star >Hind //
  ]
qed. 

lemma moves_pit: ∀S,w,i. moves S w (pit_pre S i) = pit_pre S i.
#S #w #i elim w // 
qed. 
 
lemma to_pit: ∀S,w,e. ¬ sublist S w (occur S (|\fst e|)) →
 moves S w e = pit_pre S (\fst e).
#S #w elim w
  [#e * #H @False_ind @H normalize #a #abs @False_ind /2/
  |#a #tl #Hind #e #H cases (true_or_false (memb S a (occur S (|\fst e|))))
    [#Htrue >moves_cons whd in ⊢ (???%); <(same_kernel … a) 
     @Hind >same_kernel @(not_to_not … H) #H1 #b #memb cases (orb_true_l … memb)
      [#H2 >(\P H2) // |#H2 @H1 //]
    |#Hfalse >moves_cons >not_occur_to_pit // >Hfalse /2/ 
    ]
  ]
qed.

(* bisimulation *)
definition cofinal ≝ λS.λp:(pre S)×(pre S). 
  \snd (\fst p) = \snd (\snd p).
  
theorem equiv_sem: ∀S:DeqSet.∀e1,e2:pre S. 
  \sem{e1} =1 \sem{e2} ↔ ∀w.cofinal ? 〈moves ? w e1,moves ? w e2〉.
#S #e1 #e2 % 
[#same_sem #w 
  cut (∀b1,b2. iff (b1 = true) (b2 = true) → (b1 = b2)) 
    [* * // * #H1 #H2 [@sym_eq @H1 //| @H2 //]]
  #Hcut @Hcut @iff_trans [|@decidable_sem] 
  @iff_trans [|@same_sem] @iff_sym @decidable_sem
|#H #w1 @iff_trans [||@decidable_sem] <H @iff_sym @decidable_sem]
qed.

definition occ ≝ λS.λe1,e2:pre S. 
  unique_append ? (occur S (|\fst e1|)) (occur S (|\fst e2|)).

lemma occ_enough: ∀S.∀e1,e2:pre S.
(∀w.(sublist S w (occ S e1 e2))→ cofinal ? 〈moves ? w e1,moves ? w e2〉)
 →∀w.cofinal ? 〈moves ? w e1,moves ? w e2〉.
#S #e1 #e2 #H #w
cases (decidable_sublist S w (occ S e1 e2)) [@H] -H #H
 >to_pit [2: @(not_to_not … H) #H1 #a #memba @sublist_unique_append_l1 @H1 //]
 >to_pit [2: @(not_to_not … H) #H1 #a #memba  @sublist_unique_append_l2 @H1 //]
 //
qed.

lemma equiv_sem_occ: ∀S.∀e1,e2:pre S.
(∀w.(sublist S w (occ S e1 e2))→ cofinal ? 〈moves ? w e1,moves ? w e2〉)
→ \sem{e1}=1\sem{e2}.
#S #e1 #e2 #H @(proj2 … (equiv_sem …)) @occ_enough #w @H 
qed.

definition sons ≝ λS:DeqSet.λl:list S.λp:(pre S)×(pre S). 
 map ?? (λa.〈move S a (\fst (\fst p)),move S a (\fst (\snd p))〉) l.

lemma memb_sons: ∀S,l.∀p,q:(pre S)×(pre S). memb ? p (sons ? l q) = true →
  ∃a.(move ? a (\fst (\fst q)) = \fst p ∧
      move ? a (\fst (\snd q)) = \snd p).
#S #l elim l [#p #q normalize in ⊢ (%→?); #abs @False_ind /2/] 
#a #tl #Hind #p #q #H cases (orb_true_l … H) -H
  [#H @(ex_intro … a) >(\P H) /2/ |#H @Hind @H]
qed.

definition is_bisim ≝ λS:DeqSet.λl:list ?.λalpha:list S.
  ∀p:(pre S)×(pre S). memb ? p l = true → cofinal ? p ∧ (sublist ? (sons ? alpha p) l).

lemma bisim_to_sem: ∀S:DeqSet.∀l:list ?.∀e1,e2: pre S. 
  is_bisim S l (occ S e1 e2) → memb ? 〈e1,e2〉 l = true → \sem{e1}=1\sem{e2}.
#S #l #e1 #e2 #Hbisim #Hmemb @equiv_sem_occ 
#w #Hsub @(proj1 … (Hbisim 〈moves S w e1,moves S w e2〉 ?))
lapply Hsub @(list_elim_left … w) [//]
#a #w1 #Hind #Hsub >moves_left >moves_left @(proj2 …(Hbisim …(Hind ?)))
  [#x #Hx @Hsub @memb_append_l1 //
  |cut (memb S a (occ S e1 e2) = true) [@Hsub @memb_append_l2 //] #occa 
   @(memb_map … occa)
  ]
qed.

(* the algorithm *)
let rec bisim S l n (frontier,visited: list ?) on n ≝
  match n with 
  [ O ⇒ 〈false,visited〉 (* assert false *)
  | S m ⇒ 
    match frontier with
    [ nil ⇒ 〈true,visited〉
    | cons hd tl ⇒
      if beqb (\snd (\fst hd)) (\snd (\snd hd)) then
        bisim S l m (unique_append ? (filter ? (λx.notb (memb ? x (hd::visited))) 
        (sons S l hd)) tl) (hd::visited)
      else 〈false,visited〉
    ]
  ].
  
lemma unfold_bisim: ∀S,l,n.∀frontier,visited: list ?.
  bisim S l n frontier visited =
  match n with 
  [ O ⇒ 〈false,visited〉 (* assert false *)
  | S m ⇒ 
    match frontier with
    [ nil ⇒ 〈true,visited〉
    | cons hd tl ⇒
      if beqb (\snd (\fst hd)) (\snd (\snd hd)) then
        bisim S l m (unique_append ? (filter ? (λx.notb(memb ? x (hd::visited))) 
          (sons S l hd)) tl) (hd::visited)
      else 〈false,visited〉
    ]
  ].
#S #l #n cases n // qed.
  
lemma bisim_never: ∀S,l.∀frontier,visited: list ?.
  bisim S l O frontier visited = 〈false,visited〉.
#frontier #visited >unfold_bisim // 
qed.

lemma bisim_end: ∀Sig,l,m.∀visited: list ?.
  bisim Sig l (S m) [] visited = 〈true,visited〉.
#n #visisted >unfold_bisim // 
qed.

lemma bisim_step_true: ∀Sig,l,m.∀p.∀frontier,visited: list ?.
beqb (\snd (\fst p)) (\snd (\snd p)) = true →
  bisim Sig l (S m) (p::frontier) visited = 
  bisim Sig l m (unique_append ? (filter ? (λx.notb(memb ? x (p::visited))) 
    (sons Sig l p)) frontier) (p::visited).
#Sig #l #m #p #frontier #visited #test >unfold_bisim normalize nodelta >test // 
qed.

lemma bisim_step_false: ∀Sig,l,m.∀p.∀frontier,visited: list ?.
beqb (\snd (\fst p)) (\snd (\snd p)) = false →
  bisim Sig l (S m) (p::frontier) visited = 〈false,visited〉.
#Sig #l #m #p #frontier #visited #test >unfold_bisim normalize nodelta >test // 
qed.

lemma notb_eq_true_l: ∀b. notb b = true → b = false.
#b cases b normalize //
qed.

let rec pitem_enum S (i:re S) on i ≝
  match i with
  [ z ⇒ [pz S]
  | e ⇒ [pe S]
  | s y ⇒ [ps S y; pp S y]
  | o i1 i2 ⇒ compose ??? (po S) (pitem_enum S i1) (pitem_enum S i2)
  | c i1 i2 ⇒ compose ??? (pc S) (pitem_enum S i1) (pitem_enum S i2)
  | k i ⇒ map ?? (pk S) (pitem_enum S i)
  ].
  
lemma pitem_enum_complete : ∀S.∀i:pitem S.
  memb (DeqItem S) i (pitem_enum S (|i|)) = true.
#S #i elim i 
  [1,2://
  |3,4:#c normalize >(\b (refl … c)) //
  |5,6:#i1 #i2 #Hind1 #Hind2 @(memb_compose (DeqItem S) (DeqItem S)) //
  |#i #Hind @(memb_map (DeqItem S)) //
  ]
qed.

definition pre_enum ≝ λS.λi:re S.
  compose ??? (λi,b.〈i,b〉) (pitem_enum S i) [true;false].
  
lemma pre_enum_complete : ∀S.∀e:pre S.
  memb ? e (pre_enum S (|\fst e|)) = true.
#S * #i #b @(memb_compose (DeqItem S) DeqBool ? (λi,b.〈i,b〉))
// cases b normalize //
qed.
 
definition space_enum ≝ λS.λi1,i2:re S.
  compose ??? (λe1,e2.〈e1,e2〉) (pre_enum S i1) (pre_enum S i2).

lemma space_enum_complete : ∀S.∀e1,e2: pre S.
  memb ? 〈e1,e2〉 (space_enum S (|\fst e1|) (|\fst e2|)) = true.
#S #e1 #e2 @(memb_compose … (λi,b.〈i,b〉))
// qed.

definition all_reachable ≝ λS.λe1,e2:pre S.λl: list ?.
uniqueb ? l = true ∧ 
  ∀p. memb ? p l = true → 
    ∃w.(moves S w e1 = \fst p) ∧ (moves S w e2 = \snd p). 

definition disjoint ≝ λS:DeqSet.λl1,l2.
  ∀p:S. memb S p l1 = true →  memb S p l2 = false.
        
lemma bisim_correct: ∀S.∀e1,e2:pre S.\sem{e1}=1\sem{e2} → 
 ∀l,n.∀frontier,visited:list ((pre S)×(pre S)).
 |space_enum S (|\fst e1|) (|\fst e2|)| < n + |visited|→
 all_reachable S e1 e2 visited →  
 all_reachable S e1 e2 frontier →
 disjoint ? frontier visited →
 \fst (bisim S l n frontier visited) = true.
#Sig #e1 #e2 #same #l #n elim n 
  [#frontier #visited #abs * #unique #H @False_ind @(absurd … abs)
   @le_to_not_lt @sublist_length // * #e11 #e21 #membp 
   cut ((|\fst e11| = |\fst e1|) ∧ (|\fst e21| = |\fst e2|))
   [|* #H1 #H2 <H1 <H2 @space_enum_complete]
   cases (H … membp) #w * #we1 #we2 <we1 <we2 % >same_kernel_moves //    
  |#m #HI * [#visited #vinv #finv >bisim_end //]
   #p #front_tl #visited #Hn * #u_visited #r_visited * #u_frontier #r_frontier 
   #disjoint
   cut (∃w.(moves ? w e1 = \fst p) ∧ (moves ? w e2 = \snd p)) 
    [@(r_frontier … (memb_hd … ))] #rp
   cut (beqb (\snd (\fst p)) (\snd (\snd p)) = true)
    [cases rp #w * #fstp #sndp <fstp <sndp @(\b ?) 
     @(proj1 … (equiv_sem … )) @same] #ptest 
   >(bisim_step_true … ptest) @HI -HI 
     [<plus_n_Sm //
     |% [whd in ⊢ (??%?); >(disjoint … (memb_hd …)) whd in ⊢ (??%?); //
        |#p1 #H (cases (orb_true_l … H)) [#eqp >(\P eqp) // |@r_visited]
        ]
     |whd % [@unique_append_unique @(andb_true_r … u_frontier)]
      @unique_append_elim #q #H
       [cases (memb_sons … (memb_filter_memb … H)) -H
        #a * #m1 #m2 cases rp #w1 * #mw1 #mw2 @(ex_intro … (w1@[a]))
        >moves_left >moves_left >mw1 >mw2 >m1 >m2 % // 
       |@r_frontier @memb_cons //
       ]
     |@unique_append_elim #q #H
       [@injective_notb @(filter_true … H)
       |cut ((q==p) = false) 
         [|#Hpq whd in ⊢ (??%?); >Hpq @disjoint @memb_cons //]
        cases (andb_true … u_frontier) #notp #_ @(\bf ?) 
        @(not_to_not … not_eq_true_false) #eqqp <notp <eqqp >H //
       ]
     ]
   ]  
qed.     

definition all_true ≝ λS.λl.∀p:(pre S) × (pre S). memb ? p l = true → 
  (beqb (\snd (\fst p)) (\snd (\snd p)) = true).

definition sub_sons ≝ λS,l,l1,l2.∀x:(pre S) × (pre S). 
memb ? x l1 = true → sublist ? (sons ? l x) l2. 

lemma bisim_complete: 
 ∀S,l,n.∀frontier,visited,visited_res:list ?.
 all_true S visited →
 sub_sons S l visited (frontier@visited) →
 bisim S l n frontier visited = 〈true,visited_res〉 →
 is_bisim S visited_res l ∧ sublist ? (frontier@visited) visited_res. 
#S #l #n elim n
  [#fron #vis #vis_res #_ #_ >bisim_never #H destruct
  |#m #Hind * 
    [(* case empty frontier *)
     -Hind #vis #vis_res #allv #H normalize in  ⊢ (%→?);
     #H1 destruct % #p 
      [#membp % [@(\P ?) @allv //| @H //]|#H1 @H1]
    |#hd cases (true_or_false (beqb (\snd (\fst hd)) (\snd (\snd hd))))
      [|(* case head of the frontier is non ok (absurd) *)
       #H #tl #vis #vis_res #allv >(bisim_step_false … H) #_ #H1 destruct]
     (* frontier = hd:: tl and hd is ok *)
     #H #tl #visited #visited_res #allv >(bisim_step_true … H)
     (* new_visited = hd::visited are all ok *)
     cut (all_true S (hd::visited)) 
      [#p #H1 cases (orb_true_l … H1) [#eqp >(\P eqp) @H |@allv]]
     (* we now exploit the induction hypothesis *)
     #allh #subH #bisim cases (Hind … allh … bisim) -bisim -Hind
      [#H1 #H2 % // #p #membp @H2 -H2 cases (memb_append … membp) -membp #membp
        [cases (orb_true_l … membp) -membp #membp
          [@memb_append_l2 >(\P membp) @memb_hd
          |@memb_append_l1 @sublist_unique_append_l2 // 
          ]
        |@memb_append_l2 @memb_cons //
        ] 
      |(* the only thing left to prove is the sub_sons invariant *)  
     #x #membx cases (orb_true_l … membx)
      [(* case x = hd *) 
       #eqhdx <(\P eqhdx) #xa #membxa
       (* xa is a son of x; we must distinguish the case xa 
        was already visited form the case xa is new *)
       cases (true_or_false … (memb ? xa (x::visited)))
        [(* xa visited - trivial *) #membxa @memb_append_l2 //
        |(* xa new *) #membxa @memb_append_l1 @sublist_unique_append_l1 @memb_filter_l
          [>membxa //|//]
        ]
      |(* case x in visited *)
       #H1 #xa #membxa cases (memb_append … (subH x … H1 … membxa))  
        [#H2 (cases (orb_true_l … H2)) 
          [#H3 @memb_append_l2 <(\P H3) @memb_hd
          |#H3 @memb_append_l1 @sublist_unique_append_l2 @H3
          ]
        |#H2 @memb_append_l2 @memb_cons @H2
        ]
      ]
    ]
  ]
qed.

definition equiv ≝ λSig.λre1,re2:re Sig. 
  let e1 ≝ •(blank ? re1) in
  let e2 ≝ •(blank ? re2) in
  let n ≝ S (length ? (space_enum Sig (|\fst e1|) (|\fst e2|))) in
  let sig ≝ (occ Sig e1 e2) in
  (bisim ? sig n [〈e1,e2〉] []).

theorem euqiv_sem : ∀Sig.∀e1,e2:re Sig.
   \fst (equiv ? e1 e2) = true ↔ \sem{e1} =1 \sem{e2}.
#Sig #re1 #re2 %
  [#H @eqP_trans [|@eqP_sym @re_embedding] @eqP_trans [||@re_embedding]
   cut (equiv ? re1 re2 = 〈true,\snd (equiv ? re1 re2)〉)
     [<H //] #Hcut
   cases (bisim_complete … Hcut) 
     [2,3: #p whd in ⊢ ((??%?)→?); #abs @False_ind /2/] 
   #Hbisim #Hsub @(bisim_to_sem … Hbisim) 
   @Hsub @memb_hd
  |#H @(bisim_correct ? (•(blank ? re1)) (•(blank ? re2))) 
    [@eqP_trans [|@re_embedding] @eqP_trans [|@H] @eqP_sym @re_embedding
    |// 
    |% // #p whd in ⊢ ((??%?)→?); #abs @False_ind /2/  
    |% // #p #H >(memb_single … H) @(ex_intro … ϵ) /2/
    |#p #_ normalize //
    ]
  ]
qed.

lemma eqbnat_true : ∀n,m. eqbnat n m = true ↔ n = m.
#n #m % [@eqbnat_true_to_eq | @eq_to_eqbnat_true]
qed.

definition DeqNat ≝ mk_DeqSet nat eqbnat eqbnat_true.

definition a ≝ s DeqNat O.
definition b ≝ s DeqNat (S O).
definition c ≝ s DeqNat (S (S O)).

definition exp1 ≝ ((a·b)^*·a).
definition exp2 ≝ a·(b·a)^*.
definition exp4 ≝ (b·a)^*.

definition exp6 ≝ a·(a ·a ·b^* + b^* ).
definition exp7 ≝ a · a^* · b^*.

definition exp8 ≝ a·a·a·a·a·a·a·a·(a^* ).
definition exp9 ≝ (a·a·a + a·a·a·a·a)^*.

example ex1 : \fst (equiv ? (exp8+exp9) exp9) = true.
normalize // qed.








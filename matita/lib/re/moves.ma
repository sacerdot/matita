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
include "basics/lists/listb.ma".

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
  [#i1 #i2 >move_cat #H1 #H2 whd in ⊢ (???%); <H1 <H2 //
  |#i1 #i2 >move_plus #H1 #H2 whd in ⊢ (???%); <H1 <H2 //
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
  |#i1 #i2 #HI1 #HI2 #w >(sem_cat S i1 i2) >move_cat
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
    
notation > "x ↦* E" non associative with precedence 60 for @{moves ? $x $E}.
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

theorem equiv_sem: ∀S:DeqSet.∀e1,e2:pre S. 
  iff (\sem{e1} =1 \sem{e2}) (∀w.\snd (moves ? w e1) = \snd (moves ? w e2)).
#S #e1 #e2 % 
[#same_sem #w 
  cut (∀b1,b2. iff (b1 = true) (b2 = true) → (b1 = b2)) 
    [* * // * #H1 #H2 [@sym_eq @H1 //| @H2 //]]
  #Hcut @Hcut @iff_trans [|@decidable_sem] 
  @iff_trans [|@same_sem] @iff_sym @decidable_sem
|#H #w1 @iff_trans [||@decidable_sem] <H @iff_sym @decidable_sem]
qed.

lemma moves_left : ∀S,a,w,e. 
  moves S (w@[a]) e = move S a (\fst (moves S w e)). 
#S #a #w elim w // #x #tl #Hind #e >moves_cons >moves_cons //
qed.

definition in_moves ≝ λS:DeqSet.λw.λe:pre S. \snd(w ↦* e).

(*
coinductive equiv (S:DeqSet) : pre S → pre S → Prop ≝
 mk_equiv:
  ∀e1,e2: pre S.
   \snd e1  = \snd e2 →
    (∀x. equiv S (move ? x (\fst e1)) (move ? x (\fst e2))) →
     equiv S e1 e2.
*)

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

lemma beqitem_true: ∀S,i1,i2. iff (beqitem S i1 i2 = true) (i1 = i2). 
#S #i1 elim i1
  [#i2 cases i2 [||#a|#a|#i21 #i22| #i21 #i22|#i3] % // normalize #H destruct
  |#i2 cases i2 [||#a|#a|#i21 #i22| #i21 #i22|#i3] % // normalize #H destruct
  |#x #i2 cases i2 [||#a|#a|#i21 #i22| #i21 #i22|#i3] % normalize #H destruct
    [>(\P H) // | @(\b (refl …))]
  |#x #i2 cases i2 [||#a|#a|#i21 #i22| #i21 #i22|#i3] % normalize #H destruct
    [>(\P H) // | @(\b (refl …))]
  |#i11 #i12 #Hind1 #Hind2 #i2 cases i2 [||#a|#a|#i21 #i22| #i21 #i22|#i3] %
   normalize #H destruct 
    [cases (true_or_false (beqitem S i11 i21)) #H1
      [>(proj1 … (Hind1 i21) H1) >(proj1 … (Hind2 i22)) // >H1 in H; #H @H
      |>H1 in H; normalize #abs @False_ind /2/
      ]
    |>(proj2 … (Hind1 i21) (refl …)) >(proj2 … (Hind2 i22) (refl …)) //
    ]
  |#i11 #i12 #Hind1 #Hind2 #i2 cases i2 [||#a|#a|#i21 #i22| #i21 #i22|#i3] %
   normalize #H destruct 
    [cases (true_or_false (beqitem S i11 i21)) #H1
      [>(proj1 … (Hind1 i21) H1) >(proj1 … (Hind2 i22)) // >H1 in H; #H @H
      |>H1 in H; normalize #abs @False_ind /2/
      ]
    |>(proj2 … (Hind1 i21) (refl …)) >(proj2 … (Hind2 i22) (refl …)) //
    ]
  |#i3 #Hind #i2 cases i2 [||#a|#a|#i21 #i22| #i21 #i22|#i4] %
   normalize #H destruct 
    [>(proj1 … (Hind i4) H) // |>(proj2 … (Hind i4) (refl …)) //]
  ]
qed. 

definition DeqItem ≝ λS.
  mk_DeqSet (pitem S) (beqitem S) (beqitem_true S).
  
unification hint  0 ≔ S; 
    X ≟ mk_DeqSet (pitem S) (beqitem S) (beqitem_true S)
(* ---------------------------------------- *) ⊢ 
    pitem S ≡ carr X.
    
unification hint  0 ≔ S,i1,i2; 
    X ≟ mk_DeqSet (pitem S) (beqitem S) (beqitem_true S)
(* ---------------------------------------- *) ⊢ 
    beqitem S i1 i2 ≡ eqb X i1 i2.

definition sons ≝ λS:DeqSet.λl:list S.λp:(pre S)×(pre S). 
 map ?? (λa.〈move S a (\fst (\fst p)),move S a (\fst (\snd p))〉) l.

lemma memb_sons: ∀S,l.∀p,q:(pre S)×(pre S). memb ? p (sons ? l q) = true →
  ∃a.(move ? a (\fst (\fst q)) = \fst p ∧
      move ? a (\fst (\snd q)) = \snd p).
#S #l elim l [#p #q normalize in ⊢ (%→?); #abs @False_ind /2/] 
#a #tl #Hind #p #q #H cases (orb_true_l … H) -H
  [#H @(ex_intro … a) <(proj1 … (eqb_true …)H) /2/
  |#H @Hind @H
  ]
qed.

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
 
definition visited_inv ≝ λS.λe1,e2:pre S.λvisited: list ?.
uniqueb ? visited = true ∧  
  ∀p. memb ? p visited = true → 
   (∃w.(moves S w e1 = \fst p) ∧ (moves S w e2 = \snd p)) ∧ 
   (beqb (\snd (\fst p)) (\snd (\snd p)) = true).
  
definition frontier_inv ≝ λS.λfrontier,visited.
uniqueb ? frontier = true ∧ 
∀p:(pre S)×(pre S). memb ? p frontier = true →  
  memb ? p visited = false ∧
  ∃p1.((memb ? p1 visited = true) ∧
   (∃a. move ? a (\fst (\fst p1)) = \fst p ∧ 
        move ? a (\fst (\snd p1)) = \snd p)).

(* lemma andb_true: ∀b1,b2:bool. 
  (b1 ∧ b2) = true → (b1 = true) ∧ (b2 = true).
#b1 #b2 cases b1 normalize #H [>H /2/ |@False_ind /2/].
qed.

lemma andb_true_r: ∀b1,b2:bool. 
  (b1 = true) ∧ (b2 = true) → (b1 ∧ b2) = true.
#b1 #b2 cases b1 normalize * // 
qed. *)

lemma notb_eq_true_l: ∀b. notb b = true → b = false.
#b cases b normalize //
qed.

(*
lemma notb_eq_true_r: ∀b. b = false → notb b = true.
#b cases b normalize //
qed.
 
lemma notb_eq_false_l:∀b. notb b = false → b = true.
#b cases b normalize //
qed.

lemma notb_eq_false_r:∀b. b = true → notb b = false.
#b cases b normalize //
qed. *)

(* include "arithmetics/exp.ma". *)

let rec pos S (i:re S) on i ≝ 
  match i with
  [ z ⇒ 0
  | e ⇒ 0
  | s y ⇒ 1
  | o i1 i2 ⇒ pos S i1 + pos S i2
  | c i1 i2 ⇒ pos S i1 + pos S i2
  | k i ⇒ pos S i
  ].

  
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

definition visited_inv_1 ≝ λS.λe1,e2:pre S.λvisited: list ?.
uniqueb ? visited = true ∧  
  ∀p. memb ? p visited = true → 
    ∃w.(moves S w e1 = \fst p) ∧ (moves S w e2 = \snd p). 
   
lemma bisim_ok1: ∀S.∀e1,e2:pre S.\sem{e1}=1\sem{e2} → 
 ∀l,n.∀frontier,visited:list (*(space S) *) ((pre S)×(pre S)).
 |space_enum S (|\fst e1|) (|\fst e2|)| < n + |visited|→
 visited_inv_1 S e1 e2 visited →  frontier_inv S frontier visited →
 \fst (bisim S l n frontier visited) = true.
#Sig #e1 #e2 #same #l #n elim n 
  [#frontier #visited #abs * #unique #H @False_ind @(absurd … abs)
   @le_to_not_lt @sublist_length // * #e11 #e21 #membp 
   cut ((|\fst e11| = |\fst e1|) ∧ (|\fst e21| = |\fst e2|))
   [|* #H1 #H2 <H1 <H2 @space_enum_complete]
   cases (H … membp) #w * #we1 #we2 <we1 <we2 % >same_kernel_moves //    
  |#m #HI * [#visited #vinv #finv >bisim_end //]
   #p #front_tl #visited #Hn * #u_visited #vinv * #u_frontier #finv
   cases (finv p (memb_hd …)) #Hp * #p2 * #visited_p2
   * #a * #movea1 #movea2
   cut (∃w.(moves Sig w e1 = \fst p) ∧ (moves Sig w e2 = \snd p))
     [cases (vinv … visited_p2) -vinv #w1 * #mw1 #mw2 
      @(ex_intro … (w1@[a])) % //] 
   -movea2 -movea1 -a -visited_p2 -p2 #reachp
   cut (beqb (\snd (\fst p)) (\snd (\snd p)) = true)
     [cases reachp #w * #move_e1 #move_e2 <move_e1 <move_e2
      @(\b ?) @(proj1 … (equiv_sem … )) @same] #ptest 
   >(bisim_step_true … ptest) @HI -HI 
     [<plus_n_Sm //
     |% [whd in ⊢ (??%?); >Hp whd in ⊢ (??%?); //]
       #p1 #H (cases (orb_true_l … H))
         [#eqp <(\P eqp) // 
         |#visited_p1 @(vinv … visited_p1)
         ]
     |whd % [@unique_append_unique @(andb_true_r … u_frontier)]
      @unique_append_elim #q #H
       [% 
         [@notb_eq_true_l @(filter_true … H) 
         |@(ex_intro … p) % [@memb_hd|@(memb_sons … (memb_filter_memb … H))]
         ]
       |cases (finv q ?) [|@memb_cons //]
        #nvq * #p1 * #Hp1 #reach %
         [cut ((p==q) = false) [|#Hpq whd in ⊢ (??%?); >Hpq @nvq]
          cases (andb_true … u_frontier) #notp #_ 
          @(not_memb_to_not_eq … H) @notb_eq_true_l @notp 
         |cases (proj2 … (finv q ?)) 
           [#p1 *  #Hp1 #reach @(ex_intro … p1) % // @memb_cons //
           |@memb_cons //
           ]
        ]
      ]  
    ]
  ]
qed.

definition all_true ≝ λS.λl.∀p:(pre S) × (pre S). memb ? p l = true → 
  (beqb (\snd (\fst p)) (\snd (\snd p)) = true).

definition sub_sons ≝ λS,l,l1,l2.∀x:(pre S) × (pre S).∀a:S. 
memb ? x l1 = true → memb S a l = true →
  memb ? 〈move ? a (\fst (\fst x)), move ? a (\fst (\snd x))〉 l2 = true.

lemma reachable_bisim: 
 ∀S,l,n.∀frontier,visited,visited_res:list ?.
 all_true S visited →
 sub_sons S l visited (frontier@visited) →
 bisim S l n frontier visited = 〈true,visited_res〉 → 
  (sub_sons S l visited_res visited_res ∧ 
   sublist ? visited visited_res ∧
   all_true S visited_res).
#S #l #n elim n
  [#fron #vis #vis_res #_ #_ >bisim_never #H destruct
  |#m #Hind * 
    [(* case empty frontier *)
     -Hind #vis #vis_res #allv #H normalize in  ⊢ (%→?);
     #H1 destruct % // % // #p /2 by / 
    |#hd cases (true_or_false (beqb (\snd (\fst hd)) (\snd (\snd hd))))
      [|(* case head of the frontier is non ok (absurd) *)
       #H #tl #vis #vis_res #allv >(bisim_step_false … H) #_ #H1 destruct]
     (* frontier = hd:: tl and hd is ok *)
     #H #tl #visited #visited_res #allv >(bisim_step_true … H)
     (* new_visited = hd::visited are all ok *)
     cut (all_true S (hd::visited)) 
      [#p #H1 cases (orb_true_l … H1) [#eqp <(\P eqp) @H |@allv]]
     (* we now exploit the induction hypothesis *)
     #allh #subH #bisim cases (Hind … allh … bisim) -Hind
      [* #H1 #H2 #H3 % // % // #p #H4 @H2 @memb_cons //]
     (* the only thing left to prove is the sub_sons invariant *)  
     #x #a #membx #memba
     cases (orb_true_l … membx)
      [(* case x = hd *) 
       #eqhdx >(proj1 … (eqb_true …) eqhdx)
       (* xa is the son of x w.r.t. a; we must distinguish the case xa 
        was already visited form the case xa is new *)
       letin xa ≝ 〈move S a (\fst (\fst x)), move S a (\fst (\snd x))〉
       cases (true_or_false … (memb ? xa (x::visited)))
        [(* xa visited - trivial *) #membxa @memb_append_l2 //
        |(* xa new *) #membxa @memb_append_l1 @sublist_unique_append_l1 @memb_filter_l
          [>membxa //
          |(* this can be probably improved *)
           generalize in match memba; -memba elim l
            [whd in ⊢ (??%?→?); #abs @False_ind /2/
            |#b #others #Hind #memba cases (orb_true_l … memba) #H
              [>(proj1 … (eqb_true …) H) @memb_hd
              |@memb_cons @Hind //
              ]
            ]
          ]
        ]
      |(* case x in visited *)
       #H1 letin xa ≝ 〈move S a (\fst (\fst x)), move S a (\fst (\snd x))〉
       cases (memb_append … (subH x a H1 memba))  
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

(* pit state *)
let rec blank_item (S: DeqSet) (i: re S) on i :pitem S ≝
 match i with
  [ z ⇒ `∅
  | e ⇒ ϵ
  | s y ⇒ `y
  | o e1 e2 ⇒ (blank_item S e1) + (blank_item S e2) 
  | c e1 e2 ⇒ (blank_item S e1) · (blank_item S e2)
  | k e ⇒ (blank_item S e)^* ].
 
definition pit_pre ≝ λS.λi.〈blank_item S (|i|), false〉. 

let rec occur (S: DeqSet) (i: re S) on i ≝  
  match i with
  [ z ⇒ [ ]
  | e ⇒ [ ]
  | s y ⇒ [y]
  | o e1 e2 ⇒ unique_append ? (occur S e1) (occur S e2) 
  | c e1 e2 ⇒ unique_append ? (occur S e1) (occur S e2) 
  | k e ⇒ occur S e].
  
axiom memb_single: ∀S,a,x. memb S a [x] = true → a = x.

axiom tech: ∀b. b ≠ true → b = false.
axiom tech2: ∀b. b = false → b ≠ true.

lemma not_occur_to_pit: ∀S,a.∀i:pitem S. memb S a (occur S (|i|)) = false →
  move S a i  = pit_pre S i.
#S #a #i elim i //
  [#x cases (true_or_false (a==x)) 
    [#H >(proj1 …(eqb_true …) H) whd in ⊢ ((??%?)→?); 
     >(proj2 …(eqb_true …) (refl …)) whd in ⊢ ((??%?)→?); #abs @False_ind /2/
    |#H normalize >H //
    ]
  |#i1 #i2 #Hind1 #Hind2 #H >move_cat >Hind1 [2:@tech 
   @(not_to_not … (tech2 … H)) #H1 @sublist_unique_append_l1 //]
   >Hind2 [2:@tech @(not_to_not … (tech2 … H)) #H1 @sublist_unique_append_l2 //]
   //
  |#i1 #i2 #Hind1 #Hind2 #H >move_plus >Hind1 [2:@tech 
   @(not_to_not … (tech2 … H)) #H1 @sublist_unique_append_l1 //]
   >Hind2 [2:@tech @(not_to_not … (tech2 … H)) #H1 @sublist_unique_append_l2 //]
   //
  |#i #Hind #H >move_star >Hind // @H
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
#S #w #i elim w // #a #tl >moves_cons // 
qed. 
 
lemma to_pit: ∀S,w,e. ¬ sublist S w (occur S (|\fst e|)) →
 moves S w e = pit_pre S (\fst e).
#S #w elim w
  [(* orribile *)
   #e * #H @False_ind @H normalize #a #abs @False_ind /2/
  |#a #tl #Hind #e #H cases (true_or_false (memb S a (occur S (|\fst e|))))
    [#Htrue >moves_cons whd in ⊢ (???%); <(same_kernel … a) 
     @Hind >same_kernel @(not_to_not … H) #H1 #b #memb cases (orb_true_l … memb)
      [#H2 <(proj1 … (eqb_true …) H2) // |#H2 @H1 //]
    |#Hfalse >moves_cons >not_occur_to_pit //
    ]
  ]
qed.
    
definition occ ≝ λS.λe1,e2:pre S. 
  unique_append ? (occur S (|\fst e1|)) (occur S (|\fst e2|)).

(* definition occS ≝ λS:DeqSet.λoccur.
  PSig S (λx.memb S x occur = true). *)

lemma occ_enough: ∀S.∀e1,e2:pre S.
(∀w.(sublist S w (occ S e1 e2))→
 (beqb (\snd (moves S w e1)) (\snd (moves ? w e2))) = true) \to
∀w.(beqb (\snd (moves S w e1)) (\snd (moves ? w e2))) = true.
#S #e1 #e2 #H #w
cut (sublist S w (occ S e1 e2) ∨ ¬(sublist S w (occ S e1 e2)))
[elim w 
  [%1 #a normalize in ⊢ (%→?); #abs @False_ind /2/
  |#a #tl * #subtl 
    [cases (true_or_false (memb S a (occ S e1 e2))) #memba
      [%1 whd #x #membx cases (orb_true_l … membx)
        [#eqax <(proj1 … (eqb_true …) eqax) //
        |@subtl
        ]
      |%2 @(not_to_not … (tech2 … memba)) #H1 @H1 @memb_hd
      ]
    |%2 @(not_to_not … subtl) #H1 #x #H2 @H1 @memb_cons //
    ] 
  ]
|* [@H] 
 #H >to_pit 
  [2: @(not_to_not … H) #H1 #a #memba  @sublist_unique_append_l1 @H1 //]
 >to_pit
  [2: @(not_to_not … H) #H1 #a #memba  @sublist_unique_append_l2 @H1 //]
 //
]
qed.

lemma bisim_char: ∀S.∀e1,e2:pre S.
(∀w.(beqb (\snd (moves S w e1)) (\snd (moves ? w e2))) = true) → 
\sem{e1}=1\sem{e2}.
#S #e1 #e2 #H @(proj2 … (equiv_sem …)) #w @(\P ?) @H
qed.

lemma bisim_ok2: ∀S.∀e1,e2:pre S.
 (beqb (\snd e1) (\snd e2) = true) → ∀n.
 \fst (bisim S (occ S e1 e2) n (sons S (occ S e1 e2) 〈e1,e2〉) [〈e1,e2〉]) = true → 
   \sem{e1}=1\sem{e2}.
#S #e1 #e2 #Hnil #n 
letin rsig ≝ (occ S e1 e2)
letin frontier ≝ (sons S rsig 〈e1,e2〉)
letin visited_res ≝ (\snd (bisim S rsig n frontier [〈e1,e2〉])) 
#bisim_true
cut (bisim S rsig n frontier [〈e1,e2〉] = 〈true,visited_res〉)
  [<bisim_true <eq_pair_fst_snd //] #H
cut (all_true S [〈e1,e2〉]) 
  [#p #Hp cases (orb_true_l … Hp) 
    [#eqp <(proj1 … (eqb_true …) eqp) // 
    | whd in ⊢ ((??%?)→?); #abs @False_ind /2/
    ]] #allH 
cut (sub_sons S rsig [〈e1,e2〉] (frontier@[〈e1,e2〉]))
  [#x #a #H1 cases (orb_true_l … H1) 
    [#eqx <(proj1 … (eqb_true …) eqx) #H2 @memb_append_l1 
     whd in ⊢ (??(???%)?); @(memb_map … H2)
    |whd in ⊢ ((??%?)→?); #abs @False_ind /2/
    ]
  ] #init
cases (reachable_bisim … allH init … H) * #H1 #H2 #H3
cut (∀w.sublist ? w (occ S e1 e2)→∀p.memb ? p visited_res = true → 
  memb ? 〈moves ? w (\fst p), moves ? w (\snd p)〉 visited_res = true)
  [#w elim w  [#_ #p #H4 >moves_empty >moves_empty <eq_pair_fst_snd //] 
   #a #w1 #Hind #Hsub * #e11 #e21 #visp >moves_cons >moves_cons 
   @(Hind ? 〈?,?〉) [#x #H4 @Hsub @memb_cons //] 
   @(H1 〈?,?〉) [@visp| @Hsub @memb_hd]] #all_reach
@bisim_char @occ_enough
#w #Hsub @(H3 〈?,?〉) @(all_reach w Hsub 〈?,?〉) @H2 //
qed.
  
(*
definition tt ≝ ps Bin true.
definition ff ≝ ps Bin false.
definition eps ≝ pe Bin.
definition exp1 ≝ (ff + tt · ff).
definition exp2 ≝  ff · (eps + tt).

definition exp3 ≝ move Bin true (\fst (•exp1)).
definition exp4 ≝ move Bin true (\fst (•exp2)).
definition exp5 ≝ move Bin false (\fst (•exp1)).
definition exp6 ≝ move Bin false (\fst (•exp2)). *)





(*
    ||M||  This file is part of HELM, an Hypertextual, Electronic   
    ||A||  Library of Mathematics, developed at the Computer Science 
    ||T||  Department of the University of Bologna, Italy.           
    ||I||                                                            
    ||T||  
    ||A||  
    \   /  This file is distributed under the terms of the       
     \ /   GNU General Public License Version 2   
      V_____________________________________________________________*)

include "turing/move_char.ma".
include "turing/universal/marks.ma".
include "turing/universal/tuples.ma".

definition init_cell_states ≝ initN 2.

definition ics0 : init_cell_states ≝ mk_Sig ?? 0 (leb_true_to_le 1 2 (refl …)).
definition ics1 : init_cell_states ≝ mk_Sig ?? 1 (leb_true_to_le 2 2 (refl …)).

definition init_cell ≝ 
 mk_TM STape init_cell_states
 (λp.let 〈q,a〉 ≝ p in
  match pi1 … q with
  [ O ⇒ match a with
    [ None ⇒ 〈ics1, Some ? 〈〈null,false〉,N〉〉
    | Some _ ⇒ 〈ics1, None ?〉 ]
  | S _ ⇒ 〈ics1,None ?〉 ])
 ics0 (λq.q == ics1).
 
definition R_init_cell ≝ λt1,t2.
 (∃c.current STape t1 = Some ? c ∧ t2 = t1) ∨
 (current STape t1 = None ? ∧ t2 = midtape ? (left ? t1) 〈null,false〉 (right ? t1)).
 
axiom sem_init_cell : Realize ? init_cell R_init_cell.

(*
MOVE TAPE RIGHT:

  ls # current c # table # d? rs
                     ^
  ls # current c # table # d? rs init
                         ^
  ls # current c # table # d? rs
                           ^
  ls # current c # table # d rs ----------------------
                           ^     move_l
  ls # current c # table # d rs
                         ^       swap
  ls # current c # table d # rs --------------------
                         ^
  ls # current c # table d # rs
                       ^
  ls # current c # d table # rs  sub1
                   ^
  ls # current c # d table # rs
                 ^
  ls # current c d # table # rs -------------------
                 ^               move_l
  ls # current c d # table # rs -------------------
               ^
  ls # current c d # table # rs
             ^
  ls # c current d # table # rs  sub1
       ^
  ls # c current d # table # rs
     ^
  ls c # current d # table # rs ------------------
     ^

(move_to_grid_r;)
move_r;
init_cell;
move_l;
swap;

move_l;
move_char_l;
---------move_l;
swap;

move_l;

move_l;
move_char_l;
---------move_l;
swap
*)

(* l1 # l2 r  ---> l1 r # l2 
           ^          ^
 *)
definition move_after_left_bar ≝ 
  move_l … · move_char_l STape 〈grid,false〉 · swap_r STape 〈grid,false〉.
  
definition R_move_after_left_bar ≝ λt1,t2.
  ∀l1,l2,l3,r. t1 = midtape STape (l2@〈grid,false〉::l1) r l3 → no_grids l2 → 
  t2 = midtape STape l1 r (〈grid,false〉::reverse ? l2@l3).

lemma sem_move_after_left_bar : Realize ? move_after_left_bar R_move_after_left_bar.
#intape 
cases (sem_seq … (sem_move_l …) (sem_seq … (ssem_move_char_l STape 〈grid,false〉)
        (sem_swap_r STape 〈grid,false〉)) intape)
#k * #outc * #Hloop #HR @(ex_intro ?? k) @(ex_intro ?? outc)  % [@Hloop] -Hloop
#l1 #l2 #l3  #r #Hintape #Hl2
cases HR -HR #ta * whd in ⊢ (%→?); #Hta lapply (Hta … Hintape) -Hta #Hta
* #tb * whd in ⊢(%→?); generalize in match Hta; -Hta cases l2 in Hl2;
[ #_ #Hta #Htb lapply (Htb … Hta) -Htb * #Htb lapply (Htb (refl ??)) -Htb #Htb #_
  whd in ⊢(%→?); >Htb #Houtc lapply (Houtc … Hta) -Houtc #Houtc @Houtc
| #c0 #l0 #Hnogrids #Hta #Htb lapply (Htb … Hta) -Htb * #_ #Htb
    lapply (Htb … (refl ??) ??)
    [ cases (true_or_false (memb STape 〈grid,false〉 l0)) #Hmemb
      [ @False_ind lapply (Hnogrids 〈grid,false〉 ?)
        [ @memb_cons // | normalize #Hfalse destruct (Hfalse) ]
      | @Hmemb ]
    | % #Hc0 lapply (Hnogrids c0 ?)
      [ @memb_hd | >Hc0 normalize #Hfalse destruct (Hfalse) ]
    | #Htb whd in ⊢(%→?); >Htb #Houtc lapply (Houtc … (refl ??)) -Houtc #Houtc
      >reverse_cons >associative_append @Houtc
]]
qed.

definition move_tape_r ≝ 
  move_r … · init_cell · move_l … · swap_r STape 〈grid,false〉 ·
    move_after_left_bar · move_l … · move_after_left_bar · move_r ….

definition R_move_tape_r ≝ λt1,t2.
  ∀rs,n,table,c0,bc0,curconfig,ls0.
  bit_or_null c0 = true → only_bits_or_nulls curconfig → table_TM n (reverse ? table) → 
  t1 = midtape STape (table@〈grid,false〉::〈c0,bc0〉::curconfig@〈grid,false〉::ls0) 
         〈grid,false〉 rs →
  (rs = [] ∧
   t2 = midtape STape (〈c0,bc0〉::ls0) 〈grid,false〉 (reverse STape curconfig@〈null,false〉::
                             〈grid,false〉::reverse STape table@[〈grid,false〉])) ∨
  (∃r0,rs0.rs = r0::rs0 ∧
   t2 = midtape STape (〈c0,bc0〉::ls0) 〈grid,false〉 (reverse STape curconfig@r0::
                             〈grid,false〉::reverse STape table@〈grid,false〉::rs0)).

lemma sem_move_tape_r : Realize ? move_tape_r R_move_tape_r.
#tapein 
cases (sem_seq …(sem_move_r …) (sem_seq … sem_init_cell (sem_seq … (sem_move_l …)
   (sem_seq … (sem_swap_r STape 〈grid,false〉) (sem_seq … sem_move_after_left_bar
     (sem_seq … (sem_move_l …) (sem_seq … sem_move_after_left_bar (sem_move_r …))))))) tapein)
#k * #outc * #Hloop #HR @(ex_intro ?? k) @(ex_intro ?? outc) % [@Hloop] -Hloop
#rs #n #table #c0 #bc0 #curconfig #ls0 #Hbitnullc0 #Hbitnullcc #Htable #Htapein
cases HR -HR #ta * whd in ⊢ (%→?); #Hta lapply (Hta … Htapein) -Hta #Hta
* #tb * whd in ⊢ (%→?); *
[ * #r0 *
  generalize in match Hta; generalize in match Htapein; -Htapein -Hta cases rs
  [ #_ #Hta >Hta normalize in ⊢ (%→?); #Hfalse destruct (Hfalse) ]
  #r1 #rs1 #Htapein #Hta change with (midtape ?? r1 rs1) in Hta:(???%); >Hta 
  #Hr0 whd in Hr0:(??%?); #Htb * #tc * whd in ⊢ (%→?); #Htc lapply (Htc … Htb) -Htc #Htc
  * #td * whd in ⊢ (%→?); #Htd lapply (Htd … Htc) -Htd #Htd
  * #te * whd in ⊢ (%→?); #Hte lapply (Hte … Htd ?) [ (*memb_reverse @(no_grids_in_table … Htable)*) @daemon ] -Hte #Hte
  * #tf * whd in ⊢ (%→?); #Htf lapply (Htf … Hte) -Htf #Htf
  * #tg * whd in ⊢ (%→?); #Htg lapply (Htg … Htf ?) [ #x #Hx @bit_or_null_not_grid @Hbitnullcc // ] -Htg #Htg
  whd in ⊢ (%→?); #Houtc lapply (Houtc … Htg) -Houtc #Houtc
  %2 @(ex_intro ?? r1) @(ex_intro ?? rs1) % [%] @Houtc 
| * generalize in match Hta; generalize in match Htapein; -Htapein -Hta cases rs
  [|#r1 #rs1 #_ #Hta >Hta normalize in ⊢ (%→?); #Hfalse destruct (Hfalse) ]
  #Htapein #Hta change with (rightof ???) in Hta:(???%); >Hta 
  #Hr0 whd in Hr0:(??%?); #Htb * #tc * whd in ⊢ (%→?); #Htc lapply (Htc … Htb) -Htc #Htc
  * #td * whd in ⊢ (%→?); #Htd lapply (Htd … Htc) -Htd #Htd
  * #te * whd in ⊢ (%→?); #Hte lapply (Hte … Htd ?) [(*same as above @(no_grids_in_table … Htable) *) @daemon ] -Hte #Hte
  * #tf * whd in ⊢ (%→?); #Htf lapply (Htf … Hte) -Htf #Htf
  * #tg * whd in ⊢ (%→?); #Htg lapply (Htg … Htf ?) [ #x #Hx @bit_or_null_not_grid @Hbitnullcc // ] -Htg #Htg
  whd in ⊢ (%→?); #Houtc lapply (Houtc … Htg) -Houtc #Houtc
  % % [% | @Houtc ]
qed.

(*
MOVE TAPE LEFT:

  ls d? # current c # table # rs
                            ^     move_l; adv_to_mark_l
  ls d? # current c # table # rs
                    ^             move_l; adv_to_mark_l
  ls d? # current c # table # rs
        ^                         move_l
  ls d? # current c # table # rs
     ^                            init_cell
  ls d # current c # table # rs
     ^                            mtl_aux
  ls # current c d # table # rs
                 ^                swap_r
  ls # current d c # table # rs
                 ^                mtl_aux
  ls # current d # table c # rs
                         ^        swap
  ls # current d # table # c rs
                         ^        move_l; adv_to_mark_l
  ls # current d # table # c rs
                 ^                move_l; adv_to_mark_l
  ls # current d # table # c rs
     ^
*)
definition mtl_aux ≝ 
  swap_r STape 〈grid,false〉 · move_r … · move_r … · 
    move_char_r STape 〈grid,false〉 · move_l ….
definition R_mtl_aux ≝ λt1,t2.
  ∀l1,l2,l3,r. t1 = midtape STape l1 r (〈grid,false〉::l2@〈grid,false〉::l3) → no_grids l2 → 
  t2 = midtape STape (reverse ? l2@〈grid,false〉::l1) r (〈grid,false〉::l3).

lemma sem_mtl_aux : Realize ? mtl_aux R_mtl_aux.
#intape 
cases (sem_seq … (sem_swap_r STape 〈grid,false〉) (sem_seq … (sem_move_r …)
        (sem_seq … (sem_move_r …) (sem_seq … (ssem_move_char_r STape 〈grid,false〉) 
          (sem_move_l …)))) intape)
#k * #outc * #Hloop #HR @(ex_intro ?? k) @(ex_intro ?? outc) % [@Hloop] -Hloop
#l1 #l2 #l3  #r #Hintape #Hl2
cases HR -HR #ta * whd in ⊢ (%→?); #Hta lapply (Hta … Hintape) -Hta #Hta
* #tb * whd in ⊢(%→?); #Htb lapply (Htb … Hta) -Htb -Hta whd in ⊢ (???%→?); #Htb
* #tc * whd in ⊢(%→?); #Htc lapply (Htc … Htb) -Htc -Htb cases l2 in Hl2;
[ #_ #Htc * #td * whd in ⊢(%→?); #Htd lapply (Htd … Htc) -Htd >Htc -Htc * #Htd #_
  whd in ⊢ (%→?); #Houtc lapply (Htd (refl ??)) -Htd @Houtc
| #c0 #l0 #Hnogrids #Htc * 
  #td * whd in ⊢(%→?); #Htd lapply (Htd … Htc) -Htd -Htc * #_ #Htd
  lapply (Htd … (refl ??) ??)
  [ cases (true_or_false (memb STape 〈grid,false〉 l0)) #Hmemb
    [ @False_ind lapply (Hnogrids 〈grid,false〉 ?)
      [ @memb_cons // | normalize #Hfalse destruct (Hfalse) ]
    | @Hmemb ]
  | % #Hc0 lapply (Hnogrids c0 ?)
    [ @memb_hd | >Hc0 normalize #Hfalse destruct (Hfalse) ]
  | #Htd whd in ⊢(%→?); >Htd #Houtc lapply (Houtc … (refl ??)) -Houtc #Houtc
    >reverse_cons >associative_append @Houtc
]]
qed.

definition R_ml_atml ≝ λt1,t2.
  ∀ls1,ls2,rs.no_grids ls1 → 
  t1 = midtape STape (ls1@〈grid,false〉::ls2) 〈grid,false〉 rs → 
  t2 = midtape STape ls2 〈grid,false〉 (reverse ? ls1@〈grid,false〉::rs).

lemma sem_ml_atml : 
  Realize ? ((move_l …) · (adv_to_mark_l … (λc:STape.is_grid (\fst c)))) R_ml_atml.
#intape 
cases (sem_seq … (sem_move_l …) (sem_adv_to_mark_l … (λc:STape.is_grid (\fst c))) intape)
#k * #outc * #Hloop #HR %{k} %{outc} % [@Hloop] -Hloop
#ls1 #ls2 #rs #Hnogrids #Hintape cases HR -HR
#ta * whd in ⊢ (%→?); #Hta lapply (Hta … Hintape) -Hta
cases ls1 in Hnogrids;
[ #_ #Hta whd in ⊢ (%→?); #Houtc cases (Houtc … Hta) -Houtc
  [ * #_ >Hta #Houtc @Houtc
  | * normalize in ⊢ (%→?); #Hfalse destruct (Hfalse) ]
| #c0 #l0 #Hnogrids #Hta whd in ⊢ (%→?); #Houtc cases (Houtc … Hta) -Houtc
  [ * #Hc0 lapply (Hnogrids c0 (memb_hd …)) >Hc0 #Hfalse destruct (Hfalse)
  | * #_ #Htb >reverse_cons >associative_append @Htb //
    #x #Hx @Hnogrids @memb_cons //
  ]
]
qed.

definition move_tape_l : TM STape ≝ 
  (move_l … · adv_to_mark_l … (λc:STape.is_grid (\fst c))) ·
    (move_l … · adv_to_mark_l … (λc:STape.is_grid (\fst c))) ·
     move_l … · init_cell · mtl_aux · swap_l STape 〈grid,false〉 ·
       mtl_aux ·swap_r STape 〈grid,false〉 ·
         (move_l … · adv_to_mark_l … (λc:STape.is_grid (\fst c))) ·
           (move_l … · adv_to_mark_l … (λc:STape.is_grid (\fst c))).
        
(*  seq ? (move_r …) (seq ? init_cell (seq ? (move_l …) 
   (seq ? (swap STape 〈grid,false〉) 
     (seq ? move_after_left_bar (seq ? (move_l …) move_after_left_bar))))). *)

definition R_move_tape_l ≝ λt1,t2.
  ∀rs,n,table,c0,bc0,curconfig,ls0.
  bit_or_null c0 = true → only_bits_or_nulls curconfig →
  table_TM n (reverse ? table) → only_bits ls0 → 
  t1 = midtape STape (table@〈grid,false〉::〈c0,bc0〉::curconfig@〈grid,false〉::ls0) 
         〈grid,false〉 rs →
  (ls0 = [] ∧
   t2 = midtape STape [] 〈grid,false〉 
         (reverse ? curconfig@〈null,false〉::〈grid,false〉::reverse ? table@〈grid,false〉::〈c0,bc0〉::rs)) ∨
  (∃l1,ls1. ls0 = l1::ls1 ∧
   t2 = midtape STape ls1 〈grid,false〉
         (reverse ? curconfig@l1::〈grid,false〉::reverse ? table@〈grid,false〉::〈c0,bc0〉::rs)).
   
lemma sem_move_tape_l : Realize ? move_tape_l R_move_tape_l.
#tapein 
cases (sem_seq … sem_ml_atml
  (sem_seq … sem_ml_atml
   (sem_seq … (sem_move_l …)
    (sem_seq … sem_init_cell
     (sem_seq … sem_mtl_aux 
      (sem_seq … (sem_swap_l STape 〈grid,false〉)
       (sem_seq … sem_mtl_aux
        (sem_seq … (sem_swap_r STape 〈grid,false〉)
         (sem_seq … sem_ml_atml sem_ml_atml)))))))) tapein)
#k * #outc * #Hloop #HR @(ex_intro ?? k) @(ex_intro ?? outc) % [@Hloop] -Hloop
#rs #n #table #c0 #bc0 #curconfig #ls0 #Hbitnullc0 #Hbitnullcc #Htable #Hls0 #Htapein
cases HR -HR #ta * whd in ⊢ (%→?); #Hta lapply (Hta … Htapein) 
[ @daemon (* by no_grids_in_table, manca un lemma sulla reverse *) ]
-Hta #Hta * #tb * whd in ⊢ (%→?); #Htb lapply (Htb (〈c0,bc0〉::curconfig) … Hta)
[ @daemon ] -Hta -Htb #Htb
* #tc * whd in ⊢ (%→?); #Htc lapply (Htc … Htb) -Htb -Htc #Htc
* #td * whd in ⊢ (%→?); *
[ * #c1 * generalize in match Htc; generalize in match Htapein; -Htapein -Htc
  cases ls0 in Hls0;
  [ #_ #_ #Htc >Htc normalize in ⊢ (%→?); #Hfalse destruct (Hfalse) ]
  #l1 #ls1 #Hls0 #Htapein #Htc change with (midtape ? ls1 l1 ?) in Htc:(???%); >Htc
  #Hl1 whd in Hl1:(??%?); #Htd 
  * #te * whd in ⊢ (%→?); #Hte lapply (Hte … Htd ?)
  [ (* memb_reverse *) @daemon ] -Hte -Htd >reverse_reverse #Hte
  * #tf * whd in ⊢ (%→?); #Htf lapply (Htf … Hte) -Htf -Hte #Htf
  * #tg * whd in ⊢ (%→?); #Htg lapply (Htg … Htf ?)
  [ @(no_grids_in_table … Htable) ] -Htg -Htf >reverse_reverse #Htg
  * #th * whd in ⊢ (%→?); #Hth lapply (Hth … Htg) -Hth -Htg #Hth
  * #ti * whd in ⊢ (%→?); #Hti lapply (Hti … Hth)
  [ (* memb_reverse *) @daemon ] -Hti -Hth #Hti
  whd in ⊢ (%→?); #Houtc lapply (Houtc (l1::curconfig) … Hti)
  [ #x #Hx cases (orb_true_l … Hx) -Hx #Hx
    [ >(\P Hx) lapply (Hls0 l1 (memb_hd …)) @bit_not_grid
    | lapply (Hbitnullcc ? Hx) @bit_or_null_not_grid ] ] 
  -Houtc >reverse_cons >associative_append #Houtc %2 %{l1} %{ls1} % [%] @Houtc
| * generalize in match Htc; generalize in match Htapein; -Htapein -Htc
  cases ls0
  [| #l1 #ls1 #_ #Htc >Htc normalize in ⊢ (%→?); #Hfalse destruct (Hfalse) ]
  #Htapein #Htc change with (leftof ???) in Htc:(???%); >Htc #_ #Htd 
  * #te * whd in ⊢ (%→?); #Hte lapply (Hte … Htd ?)
  [ (*memb_reverse*) @daemon ] -Hte -Htd >reverse_reverse #Hte
  * #tf * whd in ⊢ (%→?); #Htf lapply (Htf … Hte) -Htf -Hte #Htf
  * #tg * whd in ⊢ (%→?); #Htg lapply (Htg … Htf ?)
  [ @(no_grids_in_table … Htable) ] -Htg -Htf >reverse_reverse #Htg
  * #th * whd in ⊢ (%→?); #Hth lapply (Hth … Htg) -Hth -Htg #Hth
  * #ti * whd in ⊢ (%→?); #Hti lapply (Hti … Hth)
  [ (*memb_reverse*) @daemon ] -Hti -Hth #Hti
  whd in ⊢ (%→?); #Houtc lapply (Houtc (〈null,false〉::curconfig) … Hti)
  [ #x #Hx cases (orb_true_l … Hx) -Hx #Hx
    [ >(\P Hx) %
    | lapply (Hbitnullcc ? Hx) @bit_or_null_not_grid ] ] 
  -Houtc >reverse_cons >associative_append
  >reverse_cons >associative_append #Houtc % % [%] @Houtc
]
qed.

(*definition mtl_aux ≝ 
  seq ? (move_r …) (seq ? (move_char_r STape 〈grid,false〉) (move_l …)).
definition R_mtl_aux ≝ λt1,t2.
  ∀l1,l2,l3,r. t1 = midtape STape l1 r (l2@〈grid,false〉::l3) → no_grids l2 → 
  t2 = midtape STape (reverse ? l2@l1) r (〈grid,false〉::l3).

lemma sem_mtl_aux : Realize ? mtl_aux R_mtl_aux.
#intape 
cases (sem_seq … (sem_move_r …) (sem_seq … (ssem_move_char_r STape 〈grid,false〉) (sem_move_l …)) intape)
#k * #outc * #Hloop #HR @(ex_intro ?? k) @(ex_intro ?? outc) % [@Hloop] -Hloop
#l1 #l2 #l3  #r #Hintape #Hl2
cases HR -HR #ta * whd in ⊢ (%→?); #Hta lapply (Hta … Hintape) -Hta #Hta
* #tb * whd in ⊢(%→?); generalize in match Hta; -Hta cases l2 in Hl2;
[ #_ #Hta #Htb lapply (Htb … Hta) -Htb * #Htb #_ whd in ⊢ (%→?); #Houtc
  lapply (Htb (refl ??)) -Htb >Hta @Houtc
| #c0 #l0 #Hnogrids #Hta #Htb lapply (Htb … Hta) -Htb * #_ #Htb
    lapply (Htb … (refl ??) ??)
    [ cases (true_or_false (memb STape 〈grid,false〉 l0)) #Hmemb
      [ @False_ind lapply (Hnogrids 〈grid,false〉 ?)
        [ @memb_cons // | normalize #Hfalse destruct (Hfalse) ]
      | @Hmemb ]
    | % #Hc0 lapply (Hnogrids c0 ?)
      [ @memb_hd | >Hc0 normalize #Hfalse destruct (Hfalse) ]
    | #Htb whd in ⊢(%→?); >Htb #Houtc lapply (Houtc … (refl ??)) -Houtc #Houtc
      >reverse_cons >associative_append @Houtc
]]
qed.

check swap*)


(*
           by cases on current: 
             case bit false: move_tape_l
             case bit true: move_tape_r
             case null: adv_to_grid_l; move_l; adv_to_grid_l;
*)

definition lift_tape ≝ λls,c,rs.
  let 〈c0,b〉 ≝ c in
  let c' ≝ match c0 with
  [ null ⇒ None ?
  | _ ⇒ Some ? c ]
  in
  mk_tape STape ls c' rs.
  
definition sim_current_of_tape ≝ λt.
  match current STape t with
  [ None ⇒ 〈null,false〉
  | Some c0 ⇒ c0 ].


definition move_of_unialpha ≝ 
  λc.match c with
  [ bit x ⇒ match x with [ true ⇒ R | false ⇒ L ]
  | _ ⇒ N ].

definition no_nulls ≝ 
 λl:list STape.∀x.memb ? x l = true → is_null (\fst x) = false.
 
definition current_of_alpha ≝ λc:STape.
  match \fst c with [ null ⇒ None ? | _ ⇒ Some ? c ].

(* 
   no_marks (c::ls@rs) 
   only_bits (ls@rs)
   bit_or_null c
   
*)
definition legal_tape ≝ λls,c,rs.
 no_marks (c::ls@rs) ∧ only_bits (ls@rs) ∧ bit_or_null (\fst c) = true ∧
 (\fst c ≠ null ∨ ls = [] ∨ rs = []).
 
lemma legal_tape_left :
  ∀ls,c,rs.legal_tape ls c rs → 
  left ? (mk_tape STape ls (current_of_alpha c) rs) = ls.
#ls * #c #bc #rs * * * #_ #_ #_ *
[ *
  [ cases c
    [ #c' #_ %
    | * #Hfalse @False_ind /2/
    |*: #_ % ]
  | #Hls >Hls cases c // cases rs //
  ]
| #Hrs >Hrs cases c // cases ls //
]
qed.

axiom legal_tape_current :
  ∀ls,c,rs.legal_tape ls c rs → 
  current ? (mk_tape STape ls (current_of_alpha c) rs) = current_of_alpha c.

axiom legal_tape_right :
  ∀ls,c,rs.legal_tape ls c rs → 
  right ? (mk_tape STape ls (current_of_alpha c) rs) = rs.

(*
lemma legal_tape_cases : 
  ∀ls,c,rs.legal_tape ls c rs → 
  \fst c ≠ null ∨ (\fst c = null ∧ (ls = [] ∨ rs = [])).
#ls #c #rs cases c #c0 #bc0 cases c0
[ #c1 normalize #_ % % #Hfalse destruct (Hfalse)
| cases ls
  [ #_ %2 % // % %
  | #l0 #ls0 cases rs
    [ #_ %2 % // %2 %
    | #r0 #rs0 normalize * * #_ #Hrs destruct (Hrs) ]
  ]
|*: #_ % % #Hfalse destruct (Hfalse) ]
qed.

axiom legal_tape_conditions : 
  ∀ls,c,rs.(\fst c ≠ null ∨ ls = [] ∨ rs = []) → legal_tape ls c rs.
(*#ls #c #rs *
[ *
  [ >(eq_pair_fst_snd ?? c) cases (\fst c)
    [ #c0 #Hc % % %
    | * #Hfalse @False_ind /2/
    |*: #Hc % % %
    ]
  | cases ls [ * #Hfalse @False_ind /2/ ]
    #l0 #ls0 
  
  #Hc
*)
*)
 
definition R_move_tape_r_abstract ≝ λt1,t2.
  ∀rs,n,table,curc,curconfig,ls.
  is_bit curc = true → only_bits_or_nulls curconfig → table_TM n (reverse ? table) → 
  t1 = midtape STape (table@〈grid,false〉::〈curc,false〉::curconfig@〈grid,false〉::ls) 
         〈grid,false〉 rs →
  legal_tape ls 〈curc,false〉 rs → 
  ∀t1'.t1' = lift_tape ls 〈curc,false〉 rs → 
  ∃ls1,rs1,newc.
  (t2 = midtape STape ls1 〈grid,false〉 (reverse ? curconfig@〈newc,false〉::
    〈grid,false〉::reverse ? table@〈grid,false〉::rs1) ∧
   lift_tape ls1 〈newc,false〉 rs1 = 
   tape_move_right STape ls 〈curc,false〉 rs ∧ legal_tape ls1 〈newc,false〉 rs1).
   
lemma lift_tape_not_null :
  ∀ls,c,rs. is_null (\fst c) = false → 
  lift_tape ls c rs = mk_tape STape ls (Some ? c) rs.
#ls * #c0 #bc0 #rs cases c0
[|normalize in ⊢ (%→?); #Hfalse destruct (Hfalse) ]
//
qed.

axiom bit_not_null :  ∀d.is_bit d = true → is_null d = false.
 
lemma mtr_concrete_to_abstract :
  ∀t1,t2.R_move_tape_r t1 t2 → R_move_tape_r_abstract t1 t2.
#t1 #t2 whd in ⊢(%→?); #Hconcrete
#rs #n #table #curc #curconfig #ls #Hbitcurc #Hcurconfig #Htable #Ht1
* * * #Hnomarks #Hbits #Hcurc #Hlegal #t1' #Ht1'
cases (Hconcrete … Htable Ht1) //
[ * #Hrs #Ht2
  @(ex_intro ?? (〈curc,false〉::ls)) @(ex_intro ?? [])
  @(ex_intro ?? null) %
  [ %
    [ >Ht2 %
    | >Hrs % ]
  | % [ % [ %
    [ >append_nil #x #Hx cases (orb_true_l … Hx) #Hx'
      [ >(\P Hx') % 
      | @Hnomarks @(memb_append_l1 … Hx') ]
    | >append_nil #x #Hx cases (orb_true_l … Hx) #Hx'
      [ >(\P Hx') //
      | @Hbits @(memb_append_l1 … Hx') ]]
    | % ]
    | %2 % ]
  ]
| * * #r0 #br0 * #rs0 * #Hrs 
  cut (br0 = false) 
  [ @(Hnomarks 〈r0,br0〉) @memb_cons @memb_append_l2 >Hrs @memb_hd]
  #Hbr0 >Hbr0 in Hrs; #Hrs #Ht2
  @(ex_intro ?? (〈curc,false〉::ls)) @(ex_intro ?? rs0)
  @(ex_intro ?? r0) %
  [ %
    [ >Ht2  //
    | >Hrs >lift_tape_not_null
      [ %
      | @bit_not_null @(Hbits 〈r0,false〉) >Hrs @memb_append_l2 @memb_hd ] ]
  | % [ % [ %
    [ #x #Hx cases (orb_true_l … Hx) #Hx'
      [ >(\P Hx') % 
      | cases (memb_append … Hx') #Hx'' @Hnomarks 
        [ @(memb_append_l1 … Hx'') 
        | >Hrs @memb_cons @memb_append_l2 @(memb_cons … Hx'') ]
      ]
    | whd in ⊢ (?%); #x #Hx cases (orb_true_l … Hx) #Hx'
      [ >(\P Hx') //
      | cases (memb_append … Hx') #Hx'' @Hbits
        [ @(memb_append_l1 … Hx'') | >Hrs @memb_append_l2 @(memb_cons … Hx'') ]
      ]]
    | whd in ⊢ (??%?); >(Hbits 〈r0,false〉) //
      @memb_append_l2 >Hrs @memb_hd ]
    | % % % #Hr0 lapply (Hbits 〈r0,false〉?) 
      [ @memb_append_l2 >Hrs @memb_hd
      | >Hr0 normalize #Hfalse destruct (Hfalse)
      ] ] ] ]
qed.

definition R_move_tape_l_abstract ≝ λt1,t2.
  ∀rs,n,table,curc,curconfig,ls.
  is_bit curc = true → only_bits_or_nulls curconfig → table_TM n (reverse ? table) → 
  t1 = midtape STape (table@〈grid,false〉::〈curc,false〉::curconfig@〈grid,false〉::ls) 
         〈grid,false〉 rs →
  legal_tape ls 〈curc,false〉 rs → 
  ∀t1'.t1' = lift_tape ls 〈curc,false〉 rs → 
  ∃ls1,rs1,newc.
  (t2 = midtape STape ls1 〈grid,false〉 (reverse ? curconfig@〈newc,false〉::
    〈grid,false〉::reverse ? table@〈grid,false〉::rs1) ∧
   lift_tape ls1 〈newc,false〉 rs1 = 
   tape_move_left STape ls 〈curc,false〉 rs ∧ legal_tape ls1 〈newc,false〉 rs1).

lemma mtl_concrete_to_abstract :
  ∀t1,t2.R_move_tape_l t1 t2 → R_move_tape_l_abstract t1 t2.
#t1 #t2 whd in ⊢(%→?); #Hconcrete
#rs #n #table #curc #curconfig #ls #Hcurc #Hcurconfig #Htable #Ht1
* * * #Hnomarks #Hbits #Hcurc #Hlegal #t1' #Ht1'
cases (Hconcrete … Htable ? Ht1) //
[ * #Hls #Ht2
  @(ex_intro ?? [])
  @(ex_intro ?? (〈curc,false〉::rs)) 
  @(ex_intro ?? null) %
  [ %
    [ >Ht2 %
    | >Hls % ]
  |  % [ % [ %
    [ #x #Hx cases (orb_true_l … Hx) #Hx'
      [ >(\P Hx') % 
      | @Hnomarks >Hls @Hx' ]
    | #x #Hx cases (orb_true_l … Hx) #Hx'
      [ >(\P Hx') //
      | @Hbits >Hls @Hx' ]]
    | % ]
    | % %2 % ]
  ]
| * * #l0 #bl0 * #ls0 * #Hls 
  cut (bl0 = false) 
  [ @(Hnomarks 〈l0,bl0〉) @memb_cons @memb_append_l1 >Hls @memb_hd]
  #Hbl0 >Hbl0 in Hls; #Hls #Ht2
  @(ex_intro ?? ls0) @(ex_intro ?? (〈curc,false〉::rs))
  @(ex_intro ?? l0) %
  [ % 
    [ >Ht2 %
    | >Hls >lift_tape_not_null
      [ %
      | @bit_not_null @(Hbits 〈l0,false〉) >Hls @memb_append_l1 @memb_hd ] ]
  | % [ % [ %
    [ #x #Hx cases (orb_true_l … Hx) #Hx'
      [ >(\P Hx') % 
      | cases (memb_append … Hx') #Hx'' @Hnomarks 
        [ >Hls @memb_cons @memb_cons @(memb_append_l1 … Hx'') 
        | cases (orb_true_l … Hx'') #Hx'''
          [ >(\P Hx''') @memb_hd
          | @memb_cons @(memb_append_l2 … Hx''')]
        ]
      ]
    | whd in ⊢ (?%); #x #Hx cases (memb_append … Hx) #Hx'
      [ @Hbits >Hls @memb_cons @(memb_append_l1 … Hx')
      | cases (orb_true_l … Hx') #Hx''
        [ >(\P Hx'') //
        | @Hbits @(memb_append_l2 … Hx'')
        ]]]
    | whd in ⊢ (??%?); >(Hbits 〈l0,false〉) //
      @memb_append_l1 >Hls @memb_hd ]
    | % % % #Hl0 lapply (Hbits 〈l0,false〉?) 
      [ @memb_append_l1 >Hls @memb_hd
      | >Hl0 normalize #Hfalse destruct (Hfalse)
      ] ] ] 
| #x #Hx @Hbits @memb_append_l1 @Hx ]
qed. 

lemma sem_move_tape_l_abstract : Realize … move_tape_l R_move_tape_l_abstract.
@(Realize_to_Realize … mtl_concrete_to_abstract) //
qed.

lemma sem_move_tape_r_abstract : Realize … move_tape_r R_move_tape_r_abstract.
@(Realize_to_Realize … mtr_concrete_to_abstract) //
qed.

(*
 t1 =  ls # cs c # table # rs  
 
 let simt ≝ lift_tape ls c rs in
 let simt' ≝ move_left simt' in
 
 t2 = left simt'# cs (sim_current_of_tape simt') # table # right simt'
*)
          
(*
definition R_move

definition R_exec_move ≝ λt1,t2.
  ∀ls,current,table1,newcurrent,table2,rs.
  t1 = midtape STape (current@〈grid,false〉::ls) 〈grid,false〉
       (table1@〈comma,true〉::newcurrent@〈comma,false〉::move::table2@
        〈grid,false〉::rs) → 
  table_TM (table1@〈comma,false〉::newcurrent@〈comma,false〉::move::table2) →
  t2 = midtape
*)

(*

step :

if is_true(current) (* current state is final *)
   then nop
   else 
   init_match;
   match_tuple;
   if is_marked(current) = false (* match ok *)
      then exec_move; 
      else sink;
        
*)


definition move_tape ≝ 
  ifTM ? (test_char ? (λc:STape.c == 〈bit false,false〉)) 
    (* spostamento a sinistra: verificare se per caso non conviene spostarsi 
       sulla prima grid invece dell'ultima *)
    (adv_to_mark_r ? (λc:STape.is_grid (\fst c)) · move_tape_l)
    (ifTM ? (test_char ? (λc:STape.c == 〈bit true,false〉)) 
       (adv_to_mark_r ? (λc:STape.is_grid (\fst c)) · move_tape_r)
       (adv_to_mark_l ? (λc:STape.is_grid (\fst c)) ·
          move_l … · adv_to_mark_l ? (λc:STape.is_grid (\fst c)))
       tc_true) tc_true.
           
definition R_move_tape ≝ λt1,t2.
  ∀rs,n,table1,mv,table2,curc,curconfig,ls.
  bit_or_null mv = true → only_bits_or_nulls curconfig → 
  (is_bit mv = true → is_bit curc = true) → 
  table_TM n (reverse ? table1@〈mv,false〉::table2) → 
  t1 = midtape STape (table1@〈grid,false〉::〈curc,false〉::curconfig@〈grid,false〉::ls) 
         〈mv,false〉 (table2@〈grid,false〉::rs) →
  legal_tape ls 〈curc,false〉 rs → 
  ∀t1'.t1' = lift_tape ls 〈curc,false〉 rs → 
  ∃ls1,rs1,newc.
  legal_tape ls1 〈newc,false〉 rs1 ∧
  (t2 = midtape STape ls1 〈grid,false〉 (reverse ? curconfig@〈newc,false〉::
    〈grid,false〉::reverse ? table1@〈mv,false〉::table2@〈grid,false〉::rs1) ∧
   ((mv = bit false ∧ lift_tape ls1 〈newc,false〉 rs1 = tape_move_left STape ls 〈curc,false〉 rs) ∨
    (mv = bit true ∧ lift_tape ls1 〈newc,false〉 rs1 = tape_move_right STape ls 〈curc,false〉 rs) ∨
    (mv = null ∧ ls1 = ls ∧ rs1 = rs ∧ curc = newc))).
     
lemma sem_move_tape : Realize ? move_tape R_move_tape.
#intape 
cases (sem_if ? (test_char ??) … tc_true (sem_test_char ? (λc:STape.c == 〈bit false,false〉))
        (sem_seq … (sem_adv_to_mark_r ? (λc:STape.is_grid (\fst c))) sem_move_tape_l_abstract)
        (sem_if ? (test_char ??) … tc_true (sem_test_char ? (λc:STape.c == 〈bit true,false〉))
        (sem_seq … (sem_adv_to_mark_r ? (λc:STape.is_grid (\fst c))) sem_move_tape_r_abstract)
        (sem_seq … (sem_adv_to_mark_l ? (λc:STape.is_grid (\fst c)))
          (sem_seq … (sem_move_l …) (sem_adv_to_mark_l ? (λc:STape.is_grid (\fst c)))))) intape)
#k * #outc * #Hloop #HR
@(ex_intro ?? k) @(ex_intro ?? outc) % [@Hloop] -Hloop
#rs #n #table1 #mv #table2 #curc #curconfig #ls
#Hmv #Hcurconfig #Hmvcurc #Htable #Hintape #Htape #t1' #Ht1'
generalize in match HR; -HR *
[ * #ta * whd in ⊢ (%→?); #Hta cases (Hta 〈mv,false〉 ?)
  [| >Hintape % ] -Hta #Hceq #Hta lapply (\P Hceq) -Hceq #Hceq destruct (Hta Hceq)
  * #tb * whd in ⊢ (%→?); #Htb cases (Htb … Hintape) -Htb -Hintape
  [ * normalize in ⊢ (%→?); #Hfalse destruct (Hfalse) ]
  * #_ #Htb lapply (Htb … (refl ??) (refl ??) ?)
  [ @daemon ] -Htb >append_cons <associative_append #Htb
  whd in ⊢ (%→?); #Houtc lapply (Houtc … Htb … Ht1') //
  [ >reverse_append >reverse_append >reverse_reverse @Htable 
  | /2/
  ||]
  -Houtc -Htb * #ls1 * #rs1 * #newc * * #Houtc #Hnewtape #Hnewtapelegal
  @(ex_intro ?? ls1) @(ex_intro ?? rs1) @(ex_intro ?? newc) % 
  [ //
  | % 
    [ >Houtc >reverse_append >reverse_append >reverse_reverse
      >associative_append >associative_append % 
    | % % % // ]
  ]
| * #ta * whd in ⊢ (%→?); #Hta cases (Hta 〈mv,false〉 ?) 
  [| >Hintape % ] -Hta #Hcneq cut (mv ≠ bit false) 
  [ lapply (\Pf Hcneq) @not_to_not #Heq >Heq % ] -Hcneq #Hcneq #Hta destruct (Hta)
    *
    [ * #tb * whd in ⊢ (%→?);#Htb cases (Htb 〈mv,false〉 ?) 
      [| >Hintape % ] -Htb #Hceq #Htb lapply (\P Hceq) -Hceq #Hceq destruct (Htb Hceq)
      * #tc * whd in ⊢ (%→?); #Htc cases (Htc … Hintape) -Htc -Hintape
      [ * normalize in ⊢ (%→?); #Hfalse destruct (Hfalse) ]
    * #_ #Htc lapply (Htc … (refl ??) (refl ??) ?)
    [ @daemon ] -Htc >append_cons <associative_append #Htc
    whd in ⊢ (%→?); #Houtc lapply (Houtc … Htc … Ht1') //
    [ >reverse_append >reverse_append >reverse_reverse @Htable 
    | /2/ |]
    -Houtc -Htc * #ls1 * #rs1 * #newc * * #Houtc #Hnewtape #Hnewtapelegal
    @(ex_intro ?? ls1) @(ex_intro ?? rs1) @(ex_intro ?? newc) % 
    [ //
    | %
      [ >Houtc >reverse_append >reverse_append >reverse_reverse
        >associative_append >associative_append % 
      | % %2 % // ]
    ]
  | * #tb * whd in ⊢ (%→?); #Htb cases (Htb 〈mv,false〉 ?) 
    [| >Hintape % ] -Htb #Hcneq' cut (mv ≠ bit true) 
    [ lapply (\Pf Hcneq') @not_to_not #Heq >Heq % ] -Hcneq' #Hcneq' #Htb destruct (Htb)
    * #tc * whd in ⊢ (%→?); #Htc cases (Htc … Hintape)
    [ *  >(bit_or_null_not_grid … Hmv) #Hfalse destruct (Hfalse) ] -Htc
    * #_ #Htc lapply (Htc … (refl ??) (refl ??) ?) [@daemon] -Htc #Htc
    * #td * whd in ⊢ (%→?); #Htd lapply (Htd … Htc) -Htd -Htc
    whd in ⊢ (???%→?); #Htd whd in ⊢ (%→?); #Houtc lapply (Houtc … Htd) -Houtc *
    [ * cases Htape * * #_ #_ #Hcurc #_
      >(bit_or_null_not_grid … Hcurc) #Hfalse destruct (Hfalse) ]
    * #_ #Houtc lapply (Houtc … (refl ??) (refl ??) ?) [@daemon] -Houtc #Houtc
    @(ex_intro ?? ls) @(ex_intro ?? rs) @(ex_intro ?? curc) %
    [ //
    | %
      [ @Houtc
      | %2 % // % // % // 
        generalize in match Hcneq; generalize in match Hcneq'; 
        cases mv in Hmv; normalize //
        [ * #_ normalize [ #Hfalse @False_ind cases Hfalse /2/ | #_ #Hfalse @False_ind cases Hfalse /2/ ] 
        |*: #Hfalse destruct (Hfalse) ]
      ]
    ]
  ]
]
qed.
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


(* COMPARE BIT

*)

include "turing/universal/copy.ma".
include "turing/universal/move_tape.ma".
include "turing/universal/match_machines.ma".

(*

step :

if is_true(current) (* current state is final *)
   then nop
   else 
   (* init_match *)
   mark;
   adv_to_grid_r;
   move_r;
   mark;
   move_l;
   adv_to_mark_l
   (* /init_match *)
   match_tuple;
   if is_marked(current) = false (* match ok *)
      then 
           (* init_copy *)
           move_l;
           init_current;
           move_r;
           adv_to_mark_r;
           adv_mark_r;
           (* /init_copy *)
           copy;
           move_r;
           (* move_tape *)
           by cases on current: 
             case bit false: move_tape_l
             case bit true: move_tape_r
             case null: adv_to_grid_l; move_l; adv_to_grid_l;
           move_r;
           (* /move_tape *)
      else sink;
        
*)

definition init_match ≝ 
  mark ? · adv_to_mark_r ? (λc:STape.is_grid (\fst c)) · move_r ? · 
    move_r ? · mark ? · move_l ? · adv_to_mark_l ? (is_marked ?).
             
definition R_init_match ≝ λt1,t2.
  ∀ls,l,rs,c,d. no_grids (〈c,false〉::l) → no_marks l → 
  t1 = midtape STape ls 〈c,false〉 (l@〈grid,false〉::〈bar,false〉::〈d,false〉::rs) →
  t2 = midtape STape ls 〈c,true〉 (l@〈grid,false〉::〈bar,false〉::〈d,true〉::rs).
  
lemma sem_init_match : Realize ? init_match R_init_match.
#intape 
cases (sem_seq ????? (sem_mark ?)
       (sem_seq ????? (sem_adv_to_mark_r ? (λc:STape.is_grid (\fst c)))
        (sem_seq ????? (sem_move_r ?)
         (sem_seq ????? (sem_move_r ?)
          (sem_seq ????? (sem_mark ?)
           (sem_seq ????? (sem_move_l ?)
            (sem_adv_to_mark_l ? (is_marked ?))))))) intape)
#k * #outc * #Hloop #HR 
@(ex_intro ?? k) @(ex_intro ?? outc) % [@Hloop] -Hloop
#ls #l #rs #c #d #Hnogrids #Hnomarks #Hintape
cases HR -HR
#ta * whd in ⊢ (%→?); * #Hta #_ lapply (Hta … Hintape) -Hta -Hintape #Hta
* #tb * whd in ⊢ (%→?); * #_ #Htb cases (Htb … Hta) -Htb -Hta 
  [* #Hgridc @False_ind @(absurd … Hgridc) @eqnot_to_noteq 
   @(Hnogrids 〈c,false〉) @memb_hd ]
* * #Hgrdic #Htb #_ lapply (Htb l 〈grid,false〉 (〈bar,false〉::〈d,false〉::rs) (refl …) (refl …) ?) 
  [#x #membl @Hnogrids @memb_cons @membl] -Htb #Htb
* #tc * whd in ⊢ (%→?); * #_ #Htc lapply (Htc … Htb) -Htc -Htb #Htc
* #td * whd in ⊢ (%→?); * #_ #Htd lapply (Htd … Htc) -Htd -Htc #Htd
* #te * whd in ⊢ (%→?); * #Hte #_ lapply (Hte … Htd) -Hte -Htd #Hte
* #tf * whd in ⊢ (%→?); * #_ #Htf lapply (Htf … Hte) -Htf -Hte #Htf
whd in ⊢ (%→?); * #_ #Htg cases (Htg … Htf) -Htg -Htf
#_ #Htg cases (Htg (refl …)) -Htg #Htg #_
lapply (Htg (〈grid,false〉::reverse ? l) 〈c,true〉 ls (refl …) (refl …) ?) 
  [#x #membl @Hnomarks @daemon] -Htg #Htg >Htg >reverse_cons >reverse_reverse
   >associative_append %
qed.

(* init_copy 

           init_current_on_match; (* no marks in current *)
           move_r;
           adv_to_mark_r;
           adv_mark_r;

*)

definition init_copy ≝ 
  init_current_on_match · move_r ? · 
    adv_to_mark_r ? (is_marked ?) · adv_mark_r ?.

definition R_init_copy ≝ λt1,t2.
  ∀l1,l2,c,ls,d,rs. 
  no_marks l1 → no_grids l1 → 
  no_marks l2 → is_grid c = false → 
  t1 = midtape STape (l1@〈c,false〉::〈grid,false〉::ls) 〈grid,false〉 (l2@〈comma,true〉::〈d,false〉::rs) → 
  t2 = midtape STape (〈comma,false〉::(reverse ? l2)@〈grid,false〉::l1@〈c,true〉::〈grid,false〉::ls) 〈d,true〉 rs.

lemma list_last: ∀A.∀l:list A.
  l = [ ] ∨ ∃a,l1. l = l1@[a].
#A #l <(reverse_reverse ? l) cases (reverse A l)
  [%1 //
  |#a #l1 %2 @(ex_intro ?? a) @(ex_intro ?? (reverse ? l1)) //
  ]
qed.
   
lemma sem_init_copy : Realize ? init_copy R_init_copy.
#intape 
cases (sem_seq ????? sem_init_current_on_match
        (sem_seq ????? (sem_move_r ?)
          (sem_seq ????? (sem_adv_to_mark_r ? (is_marked ?))
            (sem_adv_mark_r ?))) intape)
#k * #outc * #Hloop #HR 
@(ex_intro ?? k) @(ex_intro ?? outc) % [@Hloop] -Hloop
#l1 #l2 #c #ls #d #rs #Hl1marks #Hl1grids #Hl2marks #Hc #Hintape
cases HR -HR
#ta * whd in ⊢ (%→?); #Hta lapply (Hta … Hl1grids Hc Hintape) -Hta -Hintape #Hta
* #tb * whd in ⊢ (%→?); * #_ #Htb lapply (Htb  … Hta) -Htb -Hta
generalize in match Hl1marks; -Hl1marks cases (list_last ? l1) 
  [#eql1 >eql1 #Hl1marks whd in ⊢ ((???%)→?); whd in ⊢ ((???(????%))→?); #Htb
   * #tc * whd in ⊢ (%→?); * #_ #Htc lapply (Htc  … Htb) -Htc -Htb *
    [* whd in ⊢ ((??%?)→?); #Htemp destruct (Htemp)]
   * * #_ #Htc #_ lapply (Htc … (refl …) (refl …) ?)
    [#x #membx @Hl2marks @membx]
   #Htc whd in ⊢ (%→?); * #Houtc #_ cases (Houtc (reverse ? l2@〈grid,false〉::〈c,true〉::〈grid,false〉::ls) comma)
   -Houtc #Houtc lapply (Houtc … Htc) -Houtc -Htc #Houtc #_
   >Houtc %
  |* #c1 * #tl #eql1 >eql1 #Hl1marks >reverse_append >reverse_single 
   whd in ⊢ ((???%)→?); whd in ⊢ ((???(????%))→?);
   >associative_append whd in ⊢ ((???(????%))→?); #Htb
   * #tc * whd in ⊢ (%→?); * #_ #Htc lapply (Htc  … Htb) -Htc -Htb *
    [* >Hl1marks [#Htemp destruct (Htemp)] @memb_append_l2 @memb_hd]
   * * #_ >append_cons <associative_append #Htc lapply (Htc … (refl …) (refl …) ?)
    [#x #membx cases (memb_append … membx) -membx #membx
      [cases (memb_append … membx) -membx #membx
        [@Hl1marks @memb_append_l1 @daemon
        |>(memb_single … membx) %
        ]
      |@Hl2marks @membx
      ]]
  -Htc #Htc #_ whd in ⊢ (%→?); * #Houtc #_ cases (Houtc (reverse (FinProd FSUnialpha FinBool) ((reverse STape tl@[〈grid,false〉])@l2)
     @c1::〈c,true〉::〈grid,false〉::ls) comma)
  -Houtc #Houtc lapply (Houtc … Htc) -Houtc -Htc #Houtc #_
  >Houtc >reverse_append >reverse_append >reverse_single 
  >reverse_reverse >associative_append >associative_append 
  >associative_append %
qed.
  
(* OLD 
definition init_copy ≝ 
  seq ? (adv_mark_r ?) 
    (seq ? init_current_on_match
      (seq ? (move_r ?) 
        (adv_to_mark_r ? (is_marked ?)))).

definition R_init_copy ≝ λt1,t2.
  ∀l1,l2,c,l3,d,rs. 
  no_marks l1 → no_grids l1 → 
  no_marks l2 → no_grids l2 → is_grid c = false → is_grid d =false →
  t1 = midtape STape (l1@〈grid,false〉::l2@〈c,false〉::〈grid,false〉::l3) 〈comma,true〉 (〈d,false〉::rs) → 
  t2 = midtape STape (〈comma,false〉::l1@〈grid,false〉::l2@〈c,true〉::〈grid,false〉::l3) 〈d,true〉 rs.

lemma list_last: ∀A.∀l:list A.
  l = [ ] ∨ ∃a,l1. l = l1@[a].
#A #l <(reverse_reverse ? l) cases (reverse A l)
  [%1 //
  |#a #l1 %2 @(ex_intro ?? a) @(ex_intro ?? (reverse ? l1)) //
  ]
qed.
   
lemma sem_init_copy : Realize ? init_copy R_init_copy.
#intape 
cases (sem_seq ????? (sem_adv_mark_r ?)
       (sem_seq ????? sem_init_current_on_match
        (sem_seq ????? (sem_move_r ?)
         (sem_adv_to_mark_r ? (is_marked ?)))) intape)
#k * #outc * #Hloop #HR 
@(ex_intro ?? k) @(ex_intro ?? outc) % [@Hloop] -Hloop
#l1 #l2 #c #l3 #d #rs #Hl1marks #Hl1grids #Hl2marks #Hl2grids #Hc #Hd #Hintape
cases HR -HR
#ta * whd in ⊢ (%→?); #Hta lapply (Hta … Hintape) -Hta -Hintape #Hta
* #tb * whd in ⊢ (%→?); 
>append_cons #Htb lapply (Htb (〈comma,false〉::l1) l2 c … Hta) 
  [@Hd |@Hc |@Hl2grids 
   |#x #membx cases (orb_true_l … membx) -membx #membx 
     [>(\P membx) // | @Hl1grids @membx]
  ] -Htb #Htb
* #tc * whd in ⊢ (%→?); #Htc lapply (Htc … Htb) -Htc -Htb
>reverse_append >reverse_cons cases (list_last ? l2)
  [#Hl2 >Hl2 >associative_append whd in ⊢ ((???(??%%%))→?); #Htc
   whd in ⊢ (%→?); #Htd cases (Htd … Htc) -Htd -Htc
    [* whd in ⊢ ((??%?)→?); #Habs destruct (Habs)]
   * #_ #Htf lapply (Htf … (refl …) (refl …) ?) 
    [#x >reverse_cons #membx cases (memb_append … membx) -membx #membx
      [@Hl1marks @daemon |>(memb_single … membx) //] 
    -Htf
    |#Htf >Htf >reverse_reverse >associative_append %
    ]
  |* #a * #l21 #Heq >Heq >reverse_append >reverse_single 
   >associative_append >associative_append >associative_append whd in ⊢ ((???(??%%%))→?); #Htc
   whd in ⊢ (%→?); #Htd cases (Htd … Htc) -Htd -Htc
    [* >Hl2marks [#Habs destruct (Habs) |>Heq @memb_append_l2 @memb_hd]]
   * #_ <associative_append <associative_append #Htf lapply (Htf … (refl …) (refl …) ?) 
    [#x >reverse_cons #membx cases (memb_append … membx) -membx #membx
      [cases (memb_append … membx) -membx #membx
        [@Hl2marks >Heq @memb_append_l1 @daemon
        |>(memb_single … membx) //]
      |cases (memb_append … membx) -membx #membx
        [@Hl1marks @daemon |>(memb_single … membx) //]
      ]
    | #Htf >Htf >reverse_append >reverse_reverse
      >reverse_append >reverse_reverse >associative_append 
      >reverse_single >associative_append >associative_append 
      >associative_append % 
    ]
  ]
qed. *)

definition exec_action ≝ 
  init_copy · copy · move_r … · move_tape.

definition map_move ≝ 
  λc,mv.match c with [ null ⇒ None ? | _ ⇒ Some ? 〈c,false,move_of_unialpha mv〉 ].

(* - aggiungere a legal_tape le condizioni
       only_bits ls, rs; bit_or_null c
   - ci vuole un lemma che dimostri 
       bit_or_null c1 = true    bit_or_null mv = true
       mv ≠ null → c1 ≠ null
     dal fatto che c1 e mv sono contenuti nella table
 *)

definition Pre_exec_action ≝ λt1.
  ∃n,curconfig,ls,rs,c0,c1,s0,s1,table1,newconfig,mv,table2.
  table_TM n (table1@〈comma,false〉::〈s1,false〉::newconfig@〈c1,false〉::〈comma,false〉::〈mv,false〉::table2) ∧
  no_marks curconfig ∧ only_bits (curconfig@[〈s0,false〉]) ∧
  only_bits (〈s1,false〉::newconfig) ∧ bit_or_null c1 = true ∧
  |curconfig| = |newconfig| ∧
  legal_tape ls 〈c0,false〉 rs ∧
  t1 = midtape STape (〈c0,false〉::curconfig@〈s0,false〉::〈grid,false〉::ls) 〈grid,false〉 
    (table1@〈comma,true〉::〈s1,false〉::newconfig@〈c1,false〉::〈comma,false〉::〈mv,false〉::table2@〈grid,false〉::rs).

definition R_exec_action ≝ λt1,t2.
  ∀n,curconfig,ls,rs,c0,c1,s0,s1,table1,newconfig,mv,table2.
  table_TM n (table1@〈comma,false〉::〈s1,false〉::newconfig@〈c1,false〉::〈comma,false〉::〈mv,false〉::table2) → 
  no_marks curconfig → only_bits (curconfig@[〈s0,false〉]) → 
  only_bits (〈s1,false〉::newconfig) → bit_or_null c1 = true → 
  |curconfig| = |newconfig| → 
  legal_tape ls 〈c0,false〉 rs →
  t1 = midtape STape (〈c0,false〉::curconfig@〈s0,false〉::〈grid,false〉::ls) 〈grid,false〉 
    (table1@〈comma,true〉::〈s1,false〉::newconfig@〈c1,false〉::〈comma,false〉::〈mv,false〉::table2@〈grid,false〉::rs) → 
  ∀t1'.t1' = lift_tape ls 〈c0,false〉 rs → 
  ∃ls1,rs1,c2.
  t2 = midtape STape ls1 〈grid,false〉 
    (〈s1,false〉::newconfig@〈c2,false〉::〈grid,false〉::
     table1@〈comma,false〉::〈s1,false〉::newconfig@〈c1,false〉::〈comma,false〉::〈mv,false〉::table2@〈grid,false〉::rs1) ∧   
  lift_tape ls1 〈c2,false〉 rs1 = 
  tape_move STape t1' (map_move c1 mv) ∧ legal_tape ls1 〈c2,false〉 rs1.
  
(* move the following 2 lemmata to mono.ma *)
lemma tape_move_left_eq :
  ∀A.∀t:tape A.∀c.
  tape_move ? t (Some ? 〈c,L〉) = 
  tape_move_left ? (left ? t) c (right ? t).
//
qed.

lemma tape_move_right_eq :
  ∀A.∀t:tape A.∀c.
  tape_move ? t (Some ? 〈c,R〉) = 
  tape_move_right ? (left ? t) c (right ? t).
//
qed.

lemma lift_tape_not_null : 
 ∀ls,c,bc,rs.c ≠ null → lift_tape ls 〈c,bc〉 rs = midtape ? ls 〈c,bc〉 rs.
#ls #c #bc #rs cases c //
#Hfalse @False_ind /2/
qed.

lemma merge_char_not_null :
  ∀c1,c2.c1 ≠ null → merge_char c1 c2 ≠ null.
#c1 #c2 @not_to_not cases c2
[ #c1' normalize #Hfalse destruct (Hfalse)
| normalize //
| *: normalize #Hfalse destruct (Hfalse)
]
qed.

lemma merge_char_null : ∀c.merge_char null c = c.
* //
qed.

lemma merge_char_cases : ∀c1,c2.merge_char c1 c2 = c1 ∨ merge_char c1 c2 = c2.
#c1 *
[ #c1' %2 %
| % %
| *: %2 % ]
qed.

(* lemma merge_char_c_bit :
  ∀c1,c2.is_bit c2 = true → merge_char c1 c2 = c2.
#c1 *
[ #c2' #_ %
|*: normalize #Hfalse destruct (Hfalse) ]
qed.

lemma merge_char_c_bit :
  ∀c1,c2.is_null c2 = true → merge_char c1 c2 = c1.
#c1 *
[ #c2' #_ %
|*: normalize #Hfalse destruct (Hfalse) ]
qed.

*)

(*lemma GRealize_to_Realize : 
  ∀sig,M,R.GRealize sig M (λx.True) R → Realize sig M R.
#sig #M #R #HR #t @HR //
qed.*)

lemma sem_exec_action : GRealize ? exec_action Pre_exec_action R_exec_action.
@(sem_seq_app_guarded … (Realize_to_GRealize … sem_init_copy) ???)
[3:@(sem_seq_app_guarded … sem_copy)
 [3:@(sem_seq_app_guarded … (Realize_to_GRealize … (sem_move_r STape)))
  [3:@(Realize_to_GRealize … (sem_move_tape …))
  |@(λt.True)
  |4://
  |5:@sub_reflexive]
 |@(λt.True)
 |4://
 |5:@sub_reflexive]
|4:#t1 #t2 
   * #n * #curconfig * #ls * #rs * #c0 * #c1 * #s0 * #s1 * #table1 * #newconfig 
   * #mv * #table2 * * * * * * *
   #Htable #Hcurconfig1 #Hcurconfig2 #Hnewconfig #Hc1 #Hlen #Htape #Ht1
   whd in ⊢ (%→?); >Ht1 #HR
   lapply (HR (〈c0,false〉::curconfig) table1 s0 ls s1 
              (newconfig@〈c1,false〉::〈comma,false〉::〈mv,false〉::table2@〈grid,false〉::rs) ???? (refl ??))
   [(*Hcurconfig2*) @daemon
   |(*by Htable *) @daemon
   |(*Hcurconfig2*) @daemon
   |(*Hcurconfig1*) @daemon ]
   -HR #Ht2 whd
   %{(〈grid,false〉::ls)} %{s0} %{s1} %{c0} %{c1} %{(〈mv,false〉::table2@〈grid,false〉::rs)}
   %{newconfig} %{(〈comma,false〉::reverse ? table1)} %{curconfig} >Ht2
   % [ % [ % [ % [ % [ % [ % [ % 
   [ %
   |(*by Htabel*) @daemon ]
   |(*by Htable*) @daemon ]
   |// ]
   |>Hlen % ]
   |@Hcurconfig2 ]
   |@Hnewconfig ]
   |cases Htape * * // ]
   | // ] 
   |1,2:skip]
#ta #outtape #HR #n #curconfig #ls #rs #c0 #c1 #s0 #s1 #table1 #newconfig #mv
#table2 #Htable #Hcurconfig1 #Hcurconfig2 #Hnewconfig #Hbitnullc1 #Hlen #Htape
#Hta #ta' #Hta'
cases HR -HR #tb * whd in ⊢ (%→?); #Htb 
lapply (Htb (〈c0,false〉::curconfig) table1 s0 ls s1 
            (newconfig@〈c1,false〉::〈comma,false〉::〈mv,false〉::table2@〈grid,false〉::rs)
            ???? Hta) -Htb
[ (*Hcurconfig2*) @daemon
| (*Htable*) @daemon
| (* by Htape bit_or_null c0 = true, moreover Hcurconfig2 *) @daemon
| (*Hcurconfig1*) @daemon ]
#Htb * #tc * whd in ⊢ (%→?); #Htc
lapply (Htc (〈grid,false〉::ls) s0 s1 c0 c1 (〈mv,false〉::table2@〈grid,false〉::rs) newconfig (〈comma,false〉::reverse ? table1) curconfig Htb ????????) -Htc
[9:|*:(* bit_or_null c0,c1; |curconfig| = |newconfig|*) @daemon ]
#Htc * #td * whd in ⊢ (%→?); * #_ #Htd lapply (Htd … Htc) -Htd whd in ⊢(???(??%%%)→?);#Htd
whd in ⊢ (%→?); #Houtc whd in Htd:(???%); whd in Htd:(???(??%%%));
lapply (Houtc rs n 
  (〈comma,false〉::〈c1,false〉::reverse ? newconfig@〈s1,false〉::〈comma,false〉::reverse ? table1)
  mv table2 (merge_char c0 c1) (reverse ? newconfig@[〈s1,false〉]) ls ????????)
[3: cases Htape -Htape * * #Hnomarks #Hbits #Hc0 #Hlsrs % [ % [ %
  [ #x #Hx cases (orb_true_l … Hx) #Hx'
    [ >(\P Hx') %
    | @Hnomarks @memb_cons // ]
  | @Hbits ]
  | cases (merge_char_cases c0 c1) #Hmerge >Hmerge // ]
  | cases (true_or_false (c0 == null)) #Hc0'
    [ cases Hlsrs -Hlsrs 
      [ *
        [ >(\P Hc0') * #Hfalse @False_ind /2/
        | #Hlsnil % %2 // ]
      | #Hrsnil %2 // ] 
    | % % @merge_char_not_null @(\Pf Hc0') ] ]
|4:>Htd @(eq_f3 … (midtape ?))
  [ @eq_f @eq_f >associative_append >associative_append %
  | %
  | % ]
| %
|| >reverse_cons >reverse_cons >reverse_append >reverse_reverse 
   >reverse_cons >reverse_cons >reverse_reverse
   >associative_append >associative_append >associative_append
   >associative_append >associative_append
   @Htable
| (* well formedness of table *) @daemon
| (* Hnewconfig *) @daemon
| (* bit_or_null mv = true (well formedness of table) *) @daemon
| -Houtc * #ls1 * #rs1 * #newc * #Hnewtapelegal * #Houtc *
  [ *
    [ * #Hmv #Htapemove
      @(ex_intro ?? ls1) @(ex_intro ?? rs1) @(ex_intro ?? newc)
      %
      [ %
        [ >Houtc -Houtc >reverse_append
          >reverse_reverse >reverse_single @eq_f
          >reverse_cons >reverse_cons >reverse_append >reverse_cons
          >reverse_cons >reverse_reverse >reverse_reverse
          >associative_append >associative_append
          >associative_append >associative_append
          >associative_append >associative_append %
        | >Hmv >Hta' >Htapemove 
          (* mv = bit false -→ c1 = bit ? *)
          cut (∃c1'.c1 = bit c1') [ @daemon ] * #c1' #Hc1
          >Hc1 >tape_move_left_eq >(legal_tape_left … Htape) 
          >(legal_tape_right … Htape) %
        ]
      | //
      ]
    | * #Hmv #Htapemove 
      @(ex_intro ?? ls1) @(ex_intro ?? rs1) @(ex_intro ?? newc) %
      [ %
        [ >Houtc -Houtc >reverse_append
          >reverse_reverse >reverse_single @eq_f
          >reverse_cons >reverse_cons >reverse_append >reverse_cons
          >reverse_cons >reverse_reverse >reverse_reverse
          >associative_append >associative_append
          >associative_append >associative_append
          >associative_append >associative_append %
        |>Hmv >Hta' >Htapemove 
          cut (∃c1'.c1 = bit c1') [ @daemon ] * #c1' #Hc1
          >Hc1 >tape_move_right_eq >(legal_tape_left … Htape) 
          >(legal_tape_right … Htape) %
        ]
      | //
      ]
    ]
  | * * * #Hmv #Hlseq #Hrseq #Hnewc 
    @(ex_intro ?? ls1) @(ex_intro ?? rs1) @(ex_intro ?? newc) %
    [ %
      [ >Houtc -Houtc >reverse_append
        >reverse_reverse >reverse_single @eq_f
        >reverse_cons >reverse_cons >reverse_append >reverse_cons
        >reverse_cons >reverse_reverse >reverse_reverse
        >associative_append >associative_append
        >associative_append >associative_append
        >associative_append >associative_append %
      |>Hmv >Hta' cases c1 in Hnewc;
        [ #c1' whd in ⊢ (??%?→?);#Hnewc <Hnewc
          >Hlseq >Hrseq whd in ⊢ (??%%);
          >(legal_tape_left … Htape) >(legal_tape_right … Htape) %
        | whd in ⊢ (??%?→?); #Hnewc >Hnewc >Hlseq >Hrseq %
        |*: whd in ⊢ (??%?→?);#Hnewc <Hnewc
          >Hlseq >Hrseq whd in ⊢ (??%%);
          >(legal_tape_left … Htape) >(legal_tape_right … Htape) %
        ]
      ]
    | //
    ]
  ]
]
qed.

(*
if is_false(current) (* current state is not final *)
   then init_match;
    match_tuple;
    if is_marked(current) = false (* match ok *)
      then 
           exec_action
           move_r;
      else sink;
   else nop;
*)

definition uni_step ≝ 
  ifTM ? (test_char STape (λc.\fst c == bit false))
    (single_finalTM ? 
      (init_match · match_tuple ·
        (ifTM ? (test_char ? (λc.¬is_marked ? c))
          (exec_action · move_r …)
          (nop ?) tc_true)))
    (nop ?) tc_true.

definition R_uni_step_true ≝ λt1,t2.
  ∀n,table,s0,s1,c0,c1,ls,rs,curconfig,newconfig,mv.
  0 < |table| → table_TM (S n) table → 
  match_in_table (S n) (〈s0,false〉::curconfig) 〈c0,false〉
    (〈s1,false〉::newconfig) 〈c1,false〉 〈mv,false〉 table → 
  legal_tape ls 〈c0,false〉 rs → 
  t1 = midtape STape (〈grid,false〉::ls) 〈s0,false〉 
    (curconfig@〈c0,false〉::〈grid,false〉::table@〈grid,false〉::rs) → 
  ∀t1'.t1' = lift_tape ls 〈c0,false〉 rs → 
  s0 = bit false ∧
  ∃ls1,rs1,c2.
  (t2 = midtape STape (〈grid,false〉::ls1) 〈s1,false〉 
    (newconfig@〈c2,false〉::〈grid,false〉::table@〈grid,false〉::rs1) ∧
   lift_tape ls1 〈c2,false〉 rs1 = 
   tape_move STape t1' (map_move c1 mv) ∧ legal_tape ls1 〈c2,false〉 rs1).
   
definition R_uni_step_false ≝ λt1,t2.
  ∀b. current STape t1 = Some ? 〈bit b,false〉 → b = true ∧ t2 = t1.
  
(*axiom sem_match_tuple : Realize ? match_tuple R_match_tuple.*)

definition us_acc : states ? uni_step ≝ (inr … (inl … (inr … start_nop))).

definition Pre_uni_step ≝ λt1.
  ∃n,table,s0,s1,c0,c1,ls,rs,curconfig,newconfig,mv.
  0 < |table| ∧ table_TM (S n) table ∧
  match_in_table (S n) (〈s0,false〉::curconfig) 〈c0,false〉
    (〈s1,false〉::newconfig) 〈c1,false〉 〈mv,false〉 table ∧
  legal_tape ls 〈c0,false〉 rs ∧
  t1 = midtape STape (〈grid,false〉::ls) 〈s0,false〉 
    (curconfig@〈c0,false〉::〈grid,false〉::table@〈grid,false〉::rs).
    
lemma sem_uni_step :
  accGRealize ? uni_step us_acc Pre_uni_step
     R_uni_step_true R_uni_step_false. 
@(acc_sem_if_app_guarded STape … (sem_test_char ? (λc:STape.\fst c == bit false)) 
  ? (test_char_inv …) (sem_nop …) …)
[| @(sem_seq_app_guarded … (Realize_to_GRealize … sem_init_match) ???)
  [ 5: @sub_reflexive
  | 3: @(sem_seq_app_guarded … sem_match_tuple 
         (Realize_to_GRealize … (sem_if ????????? (sem_test_char …  (λc.¬is_marked FSUnialpha c))
          (sem_seq … sem_exec_action (sem_move_r …))
          (sem_nop …))))
     [@(λx.True)
     |//
     |@sub_reflexive]
  ||| #t1 #t2 * #n * #table * #s0 * #s1 * #c0 * #c1 * #ls * #rs * #curconfig 
      * #newconfig * #mv * * * *
      #Hlen1 #Htable #Hmatch #Hlegal #Ht1
      whd in ⊢ (%→?);
      cut (∃tup,table0.table = tup@table0 ∧ tuple_TM (S n) tup)
      [@daemon]
      * #tup * #table0 * #Htableeq * #qin * #cin * #qout * #cout * #mv0
      * * * * * * * * * *
      #Hqinnomarks #_ #Hqinbits #_ #_ #_ #_ #_ #Hqinlen #_ #Htupeq
      cut (∃d,qin0.qin = 〈d,false〉::qin0)
      [ lapply Hqinlen lapply Hqinnomarks -Hqinlen -Hqinnomarks cases qin
        [ #_ normalize in ⊢ (%→?); #Hfalse destruct (Hfalse) 
        | * #d #bd #qin0 #Hqinnomarks #_ %{d} %{qin0}
          >(?:bd=false) [%]
          @(Hqinnomarks 〈d,bd〉) @memb_hd ] ]
      * #d * #qin0 #Hqineq
      #Ht2 
      lapply (Ht2 (〈grid,false〉::ls) (curconfig@[〈c0,false〉])
               (qin0@〈cin,false〉::〈comma,false〉::qout@〈cout,false〉::〈comma,false〉::〈mv0,false〉::table0@〈grid,false〉::rs) s0 d ???)
      [ >Ht1 @eq_f >associative_append @eq_f @eq_f @eq_f
        >Htableeq >Htupeq >associative_append whd in ⊢ (??%?);
        @eq_f >Hqineq >associative_append @eq_f whd in ⊢ (??%?);
        @eq_f whd in ⊢ (??%?); @eq_f
        >associative_append %
      | @daemon
      | @daemon
      ]
      #Ht2 % [| % [| % [| % [ @Ht2 ]
        %2
        (* ls0 = ls
           c = s0
           l1 = curconfig@[〈c0,false〉]
           l2 = [〈bar,false〉]
           c10 = d
           l3 = qin0@[〈cin,false〉]
           l4 = qout@〈cout,false〉::〈comma,false〉::〈mv0,false〉::table0
           rs00 = rs
           n0 = S n ?
         *)
        %{ls} %{s0} %{(curconfig@[〈c0,false〉])}
        %{([〈bar,false〉])} %{d} %{(qin0@[〈cin,false〉])}
        %{(qout@〈cout,false〉::〈comma,false〉::〈mv0,false〉::table0)}
        %{rs} %{n} @daemon (* TODO *)
      ]
     ]
    ]
   ]
 | #intape #outtape 
  #ta whd in ⊢ (%→?); #Hta #HR
  #n #fulltable #s0 #s1 #c0 #c1 #ls #rs #curconfig #newconfig #mv
  #Htable_len cut (∃t0,table. fulltable =〈bar,false〉::〈t0,false〉::table) [(* 0 < |table| *) @daemon]
  * #t0 * #table #Hfulltable >Hfulltable -fulltable 
  #Htable #Hmatch #Htape #Hintape #t1' #Ht1'
  >Hintape in Hta; * * * #c #bc *
  whd in ⊢ (??%?→?); #HSome destruct (HSome) #Hc #Hta % [@(\P Hc)]
  cases HR -HR 
  #tb * whd in ⊢ (%→?); #Htb
  lapply (Htb (〈grid,false〉::ls) (curconfig@[〈c0,false〉]) (table@〈grid,false〉::rs) c t0 ???)
  [ >Hta >associative_append %
  | @daemon
  | @daemon
  | -Hta -Htb #Htb * 
    #tc * whd in ⊢ (%→?); #Htc cases (Htc … Htable … Htb) -Htb -Htc
    [| * #Hcurrent #Hfalse @False_ind
      (* absurd by Hmatch *) @daemon
    | >(\P Hc) %
    | (* Htable (con lemma) *) @daemon
    | (* Hmatch *) @daemon
    | (* Htable *) @daemon
    | (* Htable, Hmatch → |config| = n 
       necessaria modifica in R_match_tuple, le dimensioni non corrispondono
      *) @daemon
    ]
    * #table1 * #newc * #mv1 * #table2 * #Htableeq #Htc *
    [ * #td * whd in ⊢ (%→?); >Htc -Htc * * #c2 * whd in ⊢ (??%?→?); #Hc2 destruct (Hc2) 
      #_ #Htd
      cut (newc = 〈s1,false〉::newconfig@[〈c1,false〉]) [@daemon] #Hnewc
      >Hnewc cut (mv1 = 〈mv,false〉)
      [@daemon] #Hmv1
      * #te * whd in ⊢ (%→?); #Hte
      cut (td = midtape STape (〈c0,false〉::reverse STape curconfig@〈c,false〉::〈grid,false〉::ls) 
              〈grid,false〉
              ((table1@〈bar,false〉::〈c,false〉::curconfig@[〈c0,false〉])@〈comma,true〉::〈s1,false〉::
               newconfig@〈c1,false〉::〈comma,false〉::〈mv,false〉::table2@〈grid,false〉::rs))
      [ >Htd @eq_f3 //
        [ >reverse_append >reverse_single %
        | >associative_append >associative_append normalize
          >associative_append >Hmv1 >Hnewc @eq_f @eq_f @eq_f @eq_f @eq_f @eq_f
          whd in ⊢ (??%?); >associative_append % 
        ]
      ]
      -Htd #Htd lapply (Hte … (S n) … Htd … Ht1') -Htd -Hte
      [ //
      | (*|curconfig| = |newconfig|*) @daemon
      | (* Htable → bit_or_null c1 = true *) @daemon
      | (* only_bits (〈s1,false〉::newconfig) *) @daemon
      | (* only_bits (curconfig@[〈s0,false〉]) *) @daemon
      | (* no_marks (reverse ? curconfig) *) @daemon
      | >Hmv1 in Htableeq; >Hnewc 
        >associative_append >associative_append normalize
        >associative_append >associative_append
        #Htableeq <Htableeq // ]
      * #ls1 * #rs1 * #c2 * * #Hte #Hliftte #Hlegalte
      whd in ⊢ (%→?); * #_ #Houttape lapply (Houttape … Hte) -Houttape #Houttape
      whd in Houttape:(???%); whd in Houttape:(???(??%%%));
      @ex_intro [| @(ex_intro ?? rs1) @ex_intro [| % [ % 
      [ >Houttape @eq_f @eq_f @eq_f @eq_f
        change with ((〈bar,false〉::〈t0,false〉::table)@?) in ⊢ (???%);
        >Htableeq >associative_append >associative_append 
        >associative_append normalize >associative_append
        >associative_append normalize >Hnewc <Hmv1
        >associative_append normalize >associative_append
        >Hmv1 % 
      | @Hliftte
      ]
     | //
     ]
    ]
   ] 
  | * #td * whd in ⊢ (%→%→?); >Htc * #Htd
    lapply (Htd ? (refl ??)) normalize in ⊢ (%→?);
    #Hfalse destruct (Hfalse)
  ]
 ]
| #t1 #t2 #t3 whd in ⊢ (%→%→?); #Ht1 #Ht2
  #b #Hb >Hb in Ht1; * #Hc #Ht1 lapply (Hc ? (refl ??)) -Hc #Hb' %
  // cases b in Hb'; normalize #H1 //
]
qed.

(*
@(acc_sem_if_app STape … (sem_test_char ? (λc:STape.\fst c == bit false))
   (sem_seq … sem_init_match      
     (sem_seq … sem_match_tuple        
       (sem_if … (* ????????? (sem_test_char …  (λc.¬is_marked FSUnialpha c)) *)
          (sem_seq … sem_exec_action (sem_move_r …))
          (sem_nop …))))
   (sem_nop …)
   …)
[@sem_test_char||]
[ #intape #outtape 
  #ta whd in ⊢ (%→?); #Hta #HR
  #n #fulltable #s0 #s1 #c0 #c1 #ls #rs #curconfig #newconfig #mv
  #Htable_len cut (∃t0,table. fulltable =〈bar,false〉::〈t0,false〉::table) [(* 0 < |table| *) @daemon]
  * #t0 * #table #Hfulltable >Hfulltable -fulltable 
  #Htable #Hmatch #Htape #Hintape #t1' #Ht1'
  >Hintape in Hta; * * * #c #bc *
  whd in ⊢ (??%?→?); #HSome destruct (HSome) #Hc #Hta % [@(\P Hc)]
  cases HR -HR 
  #tb * whd in ⊢ (%→?); #Htb
  lapply (Htb (〈grid,false〉::ls) (curconfig@[〈c0,false〉]) (table@〈grid,false〉::rs) c t0 ???)
  [ >Hta >associative_append %
  | @daemon
  | @daemon
  | -Hta -Htb #Htb * 
    #tc * whd in ⊢ (%→?); #Htc cases (Htc … Htable … Htb) -Htb -Htc
    [| * #Hcurrent #Hfalse @False_ind
      (* absurd by Hmatch *) @daemon
    | >(\P Hc) %
    | (* Htable (con lemma) *) @daemon
    | (* Hmatch *) @daemon
    | (* Htable *) @daemon
    | (* Htable, Hmatch → |config| = n 
       necessaria modifica in R_match_tuple, le dimensioni non corrispondono
      *) @daemon
    ]
    * #table1 * #newc * #mv1 * #table2 * #Htableeq #Htc *
    [ * #td * whd in ⊢ (%→?); >Htc -Htc * * #c2 * whd in ⊢ (??%?→?); #Hc2 destruct (Hc2) 
      #_ #Htd
      cut (newc = 〈s1,false〉::newconfig@[〈c1,false〉]) [@daemon] #Hnewc
      >Hnewc cut (mv1 = 〈mv,false〉)
      [@daemon] #Hmv1
      * #te * whd in ⊢ (%→?); #Hte
      cut (td = midtape STape (〈c0,false〉::reverse STape curconfig@〈c,false〉::〈grid,false〉::ls) 
              〈grid,false〉
              ((table1@〈bar,false〉::〈c,false〉::curconfig@[〈c0,false〉])@〈comma,true〉::〈s1,false〉::
               newconfig@〈c1,false〉::〈comma,false〉::〈mv,false〉::table2@〈grid,false〉::rs))
      [ >Htd @eq_f3 //
        [ >reverse_append >reverse_single %
        | >associative_append >associative_append normalize
          >associative_append >Hmv1 >Hnewc @eq_f @eq_f @eq_f @eq_f @eq_f @eq_f
          whd in ⊢ (??%?); >associative_append % 
        ]
      ]
      -Htd #Htd lapply (Hte … (S n) … Htd … Ht1') -Htd -Hte
      [ //
      | (*|curconfig| = |newconfig|*) @daemon
      | (* Htable → bit_or_null c1 = true *) @daemon
      | (* only_bits (〈s1,false〉::newconfig) *) @daemon
      | (* only_bits (curconfig@[〈s0,false〉]) *) @daemon
      | (* no_marks (reverse ? curconfig) *) @daemon
      | >Hmv1 in Htableeq; >Hnewc 
        >associative_append >associative_append normalize
        >associative_append >associative_append
        #Htableeq <Htableeq // ]
      * #ls1 * #rs1 * #c2 * * #Hte #Hliftte #Hlegalte
      whd in ⊢ (%→?); * #_ #Houttape lapply (Houttape … Hte) -Houttape #Houttape
      whd in Houttape:(???%); whd in Houttape:(???(??%%%));
      @ex_intro [| @(ex_intro ?? rs1) @ex_intro [| % [ % 
      [ >Houttape @eq_f @eq_f @eq_f @eq_f
        change with ((〈bar,false〉::〈t0,false〉::table)@?) in ⊢ (???%);
        >Htableeq >associative_append >associative_append 
        >associative_append normalize >associative_append
        >associative_append normalize >Hnewc <Hmv1
        >associative_append normalize >associative_append
        >Hmv1 % 
      | @Hliftte
      ]
     | //
     ]
    ]
   ] 
  | * #td * whd in ⊢ (%→%→?); >Htc * #Htd
    lapply (Htd ? (refl ??)) normalize in ⊢ (%→?);
    #Hfalse destruct (Hfalse)
  ]
 ]
| #t1 #t2 #t3 whd in ⊢ (%→%→?); #Ht1 #Ht2
  #b #Hb >Hb in Ht1; * #Hc #Ht1 lapply (Hc ? (refl ??)) -Hc #Hb' %
  // cases b in Hb'; normalize #H1 //
]
qed.
*)
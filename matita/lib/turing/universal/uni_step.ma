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
  seq ? (mark ?) 
    (seq ? (adv_to_mark_r ? (λc:STape.is_grid (\fst c)))
      (seq ? (move_r ?) 
        (seq ? (mark ?)
          (seq ? (move_l ?) 
            (adv_to_mark_l ? (is_marked ?)))))).
            
definition R_init_match ≝ λt1,t2.
  ∀ls,l,rs,c,d. no_grids (〈c,false〉::l) → no_marks l → 
  t1 = midtape STape ls 〈c,false〉 (l@〈grid,false〉::〈d,false〉::rs) →
  t2 = midtape STape ls 〈c,true〉 (l@〈grid,false〉::〈d,true〉::rs).
  
lemma sem_init_match : Realize ? init_match R_init_match.
#intape 
cases (sem_seq ????? (sem_mark ?)
       (sem_seq ????? (sem_adv_to_mark_r ? (λc:STape.is_grid (\fst c)))
        (sem_seq ????? (sem_move_r ?)
         (sem_seq ????? (sem_mark ?)
          (sem_seq ????? (sem_move_l ?)
           (sem_adv_to_mark_l ? (is_marked ?)))))) intape)
#k * #outc * #Hloop #HR 
@(ex_intro ?? k) @(ex_intro ?? outc) % [@Hloop] -Hloop
#ls #l #rs #c #d #Hnogrids #Hnomarks #Hintape
cases HR -HR
#ta * whd in ⊢ (%→?); #Hta lapply (Hta … Hintape) -Hta -Hintape #Hta
* #tb * whd in ⊢ (%→?); #Htb cases (Htb … Hta) -Htb -Hta 
  [* #Hgridc @False_ind @(absurd … Hgridc) @eqnot_to_noteq 
   @(Hnogrids 〈c,false〉) @memb_hd ]
* #Hgrdic #Htb lapply (Htb l 〈grid,false〉 (〈d,false〉::rs) (refl …) (refl …) ?) 
  [#x #membl @Hnogrids @memb_cons @membl] -Htb #Htb
* #tc * whd in ⊢ (%→?); #Htc lapply (Htc … Htb) -Htc -Htb #Htc
* #td * whd in ⊢ (%→?); #Htd lapply (Htd … Htc) -Htd -Htc #Htd
* #te * whd in ⊢ (%→?); #Hte lapply (Hte … Htd) -Hte -Htd #Hte
whd in ⊢ (%→?); #Htf cases (Htf … Hte) -Htf -Hte 
  [* whd in ⊢ ((??%?)→?); #Habs destruct (Habs)]
* #_ #Htf lapply (Htf (reverse ? l) 〈c,true〉 ls (refl …) (refl …) ?) 
  [#x #membl @Hnomarks @daemon] -Htf #Htf >Htf >reverse_reverse %
qed.

(* init_copy 

           adv_mark_r;
           init_current_on_match; (* no marks in current *)
           move_r;
           adv_to_mark_r;
*)
     
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
qed.

include "turing/universal/move_tape.ma".

definition exec_move ≝ 
  seq ? (adv_to_mark_r … (is_marked ?))
    (seq ? init_copy
      (seq ? copy
        (seq ? (move_r …)
          (seq ? move_tape (move_r …))))).

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

definition mk_tuple ≝ λc,newc,mv.
  c @ 〈comma,false〉:: newc @ 〈comma,false〉 :: [〈mv,false〉].

inductive match_in_table (c,newc:list STape) (mv:unialpha) : list STape → Prop ≝ 
| mit_hd : 
   ∀tb.
   match_in_table c newc mv (mk_tuple c newc mv@〈bar,false〉::tb)
| mit_tl :
   ∀c0,newc0,mv0,tb.
   match_in_table c newc mv tb → 
   match_in_table c newc mv (mk_tuple c0 newc0 mv0@〈bar,false〉::tb).

definition move_of_unialpha ≝ 
  λc.match c with
  [ bit x ⇒ match x with [ true ⇒ R | false ⇒ L ]
  | _ ⇒ N ].

definition R_uni_step ≝ λt1,t2.
  ∀n,table,c,c1,ls,rs,curs,curc,news,newc,mv.
  table_TM n table → 
  match_in_table (〈c,false〉::curs@[〈curc,false〉]) 
    (〈c1,false〉::news@[〈newc,false〉]) mv table → 
  t1 = midtape STape (〈grid,false〉::ls) 〈c,false〉 
    (curs@〈curc,false〉::〈grid,false〉::table@〈grid,false〉::rs) → 
  ∀t1',ls1,rs1.t1' = lift_tape ls 〈curc,false〉 rs → 
  (t2 = midtape STape (〈grid,false〉::ls1) 〈c1,false〉 
    (news@〈newc,false〉::〈grid,false〉::table@〈grid,false〉::rs1) ∧
   lift_tape ls1 〈newc,false〉 rs1 = 
   tape_move STape t1' (Some ? 〈〈newc,false〉,move_of_unialpha mv〉)).

definition no_nulls ≝ 
 λl:list STape.∀x.memb ? x l = true → is_null (\fst x) = false.
 
definition R_move_tape_r_abstract ≝ λt1,t2.
  ∀rs,n,table,curc,curconfig,ls.
  bit_or_null curc = true → only_bits_or_nulls curconfig → table_TM n table → 
  t1 = midtape STape (table@〈grid,false〉::〈curc,false〉::curconfig@〈grid,false〉::ls) 
         〈grid,false〉 rs →
  no_nulls rs → 
  ∀t1'.t1' = lift_tape ls 〈curc,false〉 rs → 
  ∃ls1,rs1,newc.
  (t2 = midtape STape ls1 〈grid,false〉 (reverse ? curconfig@newc::
    〈grid,false〉::reverse ? table@〈grid,false〉::rs1) ∧
   lift_tape ls1 newc rs1 = 
   tape_move_right STape ls 〈curc,false〉 rs).
   
lemma lift_tape_not_null :
  ∀ls,c,rs. is_null (\fst c) = false → 
  lift_tape ls c rs = mk_tape STape ls (Some ? c) rs.
#ls * #c0 #bc0 #rs cases c0
[|normalize in ⊢ (%→?); #Hfalse destruct (Hfalse) ]
//
qed.
 
lemma mtr_concrete_to_abstract :
  ∀t1,t2.R_move_tape_r t1 t2 → R_move_tape_r_abstract t1 t2.
#t1 #t2 whd in ⊢(%→?); #Hconcrete
#rs #n #table #curc #curconfig #ls #Hcurc #Hcurconfig #Htable #Ht1
#Hrsnonulls #t1' #Ht1'
cases (Hconcrete … Htable Ht1) //
[ * #Hrs #Ht2
  @(ex_intro ?? (〈curc,false〉::ls)) @(ex_intro ?? [])
  @(ex_intro ?? 〈null,false〉) %
  [ >Ht2 %
  | >Hrs % ]
| * #r0 * #rs0 * #Hrs #Ht2 
  @(ex_intro ?? (〈curc,false〉::ls)) @(ex_intro ?? rs0)
  @(ex_intro ?? r0) %
  [ >Ht2 %
  | >Hrs >lift_tape_not_null
    [ %
    | @Hrsnonulls >Hrs @memb_hd ] ]
qed.
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
    ]-Htf
qed.

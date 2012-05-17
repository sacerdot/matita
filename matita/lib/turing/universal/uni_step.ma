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

#Htb lapply (Htb ??? (refl …) (refl …))

lapply (Htb l 〈grid,false〉 (〈d,false〉::rs) (refl … ))
   
 
* #tc * whd in ⊢ (%→?); #Htc 
* #td * whd in ⊢ (%→%→?); #Htd #Houtc
#l1 #c #l2 #b #l3 #c1 #rs #c0 #b0 #Hl1 #Hl2 #Hc #Hc0 #Hintape
cases (Hta … Hintape) [ * #Hfalse normalize in Hfalse; destruct (Hfalse) ]
-Hta * #_ #Hta lapply (Hta l1 〈c,true〉 ? (refl ??) ??) [@Hl1|%]
-Hta #Hta lapply (Htb … Hta) -Htb #Htb cases (Htc … Htb) [ >Hc -Hc * #Hc destruct (Hc) ] 
-Htc * #_ #Htc lapply (Htc … (refl ??) (refl ??) ?) [@Hl2]
-Htc #Htc lapply (Htd … Htc) -Htd
>reverse_append >reverse_cons 
>reverse_cons in Hc0; cases (reverse … l2)
[ normalize in ⊢ (%→?); #Hc0 destruct (Hc0)
  #Htd >(Houtc … Htd) %
| * #c2 #b2 #tl2 normalize in ⊢ (%→?);
  #Hc0 #Htd >(Houtc … Htd)
  whd in ⊢ (???%); destruct (Hc0)
  >associative_append >associative_append %
]
qed.

definition match_tuple_step ≝ 
  ifTM ? (test_char ? (λc:STape.¬ is_grid (\fst c))) 
   (single_finalTM ? 
     (seq ? compare
      (ifTM ? (test_char ? (λc:STape.is_grid (\fst c)))
        (nop ?)
        (seq ? mark_next_tuple 
           (ifTM ? (test_char ? (λc:STape.is_grid (\fst c)))
             (mark ?) (seq ? (move_l ?) init_current) tc_true)) tc_true)))
    (nop ?) tc_true.
          
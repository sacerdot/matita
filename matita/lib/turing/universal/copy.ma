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

include "turing/universal/tuples.ma".

definition write_states ≝ initN 2.

definition write ≝ λalpha,c.
  mk_TM alpha write_states
  (λp.let 〈q,a〉 ≝ p in
    match q with 
    [ O ⇒ 〈1,Some ? 〈c,N〉〉
    | S _ ⇒ 〈1,None ?〉 ])
  O (λx.x == 1).
  
definition R_write ≝ λalpha,c,t1,t2.
  ∀ls,x,rs.t1 = midtape alpha ls x rs → t2 = midtape alpha ls c rs.
  
axiom sem_write : ∀alpha,c.Realize ? (write alpha c) (R_write alpha c).

definition copy_step_subcase ≝
  λalpha,c,elseM.ifTM ? (test_char ? (λx.x == 〈c,true〉))
    (seq (FinProd alpha FinBool) (adv_mark_r …)
      (seq ? (move_l …)
        (seq ? (adv_to_mark_l … (is_marked alpha))
          (seq ? (write ? 〈c,false〉)
            (seq ? (move_r …)
              (seq ? (mark …)
                (seq ? (move_r …) (adv_to_mark_r … (is_marked alpha)))))))))
    elseM tc_true.

definition R_copy_step_subcase ≝ 
  λalpha,c,RelseM,t1,t2.
    ∀a,l1,x0,a0,l2,x,l3.
    t1 = midtape (FinProd … alpha FinBool) (l1@〈a0,false〉::〈x0,true〉::l2) 
         〈x,true〉 (〈a,false〉::l3) → 
    (∀c.memb ? c l1 = true → is_marked ? c = false) →          
    (x = c ∧ t2 = midtape ? (〈x,false〉::l1@〈a0,true〉::〈x,false〉::l2) 〈a,true〉 l3) ∨
    (x ≠ c ∧ RelseM t1 t2).
    
axiom sem_copy_step_subcase : 
  ∀alpha,c,elseM,RelseM.
  Realize ? (copy_step_subcase alpha c elseM) (R_copy_step_subcase alpha c RelseM).
    
(*
if current = 0,tt
   then advance_mark_r;
        move_l;
        advance_to_mark_l;
        write(0,ff)
        move_r;
        mark;
        move_r;
        advance_to_mark_r;
else if current = 1,tt
   then advance_mark_r;
        move_l;
        advance_to_mark_l;
        write(1,ff)
        move_r;
        mark;
        move_r;
        advance_to_mark_r;
else if current = null 
   then advance_mark_r;
        move_l;
        advance_to_mark_l
        adv_mark_r;
        move_r;
        advance_to_mark_r
*)

definition nocopy_subcase ≝
  ifTM STape (test_char ? (λx:STape.x == 〈null,true〉))
    (seq ? (adv_mark_r …)
      (seq ? (move_l …)
        (seq ? (adv_to_mark_l … (is_marked ?))
          (seq ? (adv_mark_r …)
            (seq ? (move_r …) (adv_to_mark_r … (is_marked ?)))))))
    (nop ?) tc_true.

definition R_nocopy_subcase ≝ 
  λt1,t2.
    ∀a,l1,x0,a0,l2,x,l3.
    t1 = midtape STape (l1@〈a0,false〉::〈x0,true〉::l2) 
         〈x,true〉 (〈a,false〉::l3) → 
    (∀c.memb ? c l1 = true → is_marked ? c = false) →          
    (x = null ∧
     t2 = midtape ? (〈x,false〉::l1@〈a0,true〉::〈x0,false〉::l2) 〈a,true〉 l3) ∨
    (x ≠ null ∧ t2 = t1).
    
axiom sem_nocopy_subcase : Realize ? nocopy_subcase R_nocopy_subcase.
(* #intape
cases (sem_if ? (test_char ? (λx:STape.x == 〈null,true〉)) ?????? tc_true
 (sem_test_char ? (λx:STape.x == 〈null,true〉))
        (sem_seq … (sem_adv_mark_r …)
           (sem_seq … (sem_move_l …)
             (sem_seq … (sem_adv_to_mark_l … (is_marked ?))
               (sem_seq … (sem_adv_mark_r …)
                 (sem_seq … (sem_move_r …) (sem_adv_to_mark_r … (is_marked ?))
                 ))))) (sem_nop ?) intape)
#k * #outc * #Hloop #HR @(ex_intro ?? k) @(ex_intro ?? outc)  % [@Hloop] -Hloop
cases HR -HR
[| * #ta * whd in ⊢ (%→%→?); #Hta #Houtc
   #ls #x #rs #Hintape %2  >Hintape in Hta; #Hta cases (Hta ? (refl ??)) -Hta #Hx #Hta %
   [ lapply (\Pf Hx) @not_to_not #Hx' >Hx' %
   | <Hta @Houtc ] ]
@daemon
qed. *)

definition copy_step ≝
  ifTM ? (test_char STape (λc.is_bit (\fst c)))
  (single_finalTM ? (copy_step_subcase FSUnialpha (bit false)
    (copy_step_subcase FSUnialpha (bit true) nocopy_subcase)))
  (nop ?)
  tc_true.
  
definition R_copy_step_true ≝ 
  λt1,t2.
    ∀a,l1,x0,a0,l2,c,l3.
    t1 = midtape STape (l1@〈a0,false〉::〈x0,true〉::l2) 
         〈c,true〉 (〈a,false〉::l3) → 
    (∀c.memb ? c l1 = true → is_marked ? c = false) →          
    (∃x. c = bit x ∧
    t2 = midtape STape (〈bit x,false〉::l1@〈a0,true〉::〈bit x,false〉::l2) 〈a,true〉 l3) ∨
    (c = null ∧
     t2 = midtape ? (〈null,false〉::l1@〈a0,true〉::〈x0,false〉::l2) 〈a,true〉 l3).
     
definition R_copy_step_false ≝ 
  λt1,t2.
   ∀ls,c,rs.t1 = midtape (FinProd … FSUnialpha FinBool) ls c rs → 
   bit_or_null (\fst c) = false ∧ t2 = t1.

axiom sem_comp_step : 
  accRealize ? copy_step (inr … (inl … (inr … 0))) R_copy_step_true R_copy_step_false.

(*
1) il primo carattere è marcato
2) l'ultimo carattere è l'unico che può essere null, gli altri sono bit
3) il terminatore non è né bit, né null
*)
   
definition copy0 ≝ whileTM ? copy_step (inr … (inl … (inr … 0))).

let rec merge_config (l1,l2:list STape) ≝ 
  match l1 with
  [ nil ⇒ nil ?
  | cons p1 l1' ⇒ match l2 with
    [ nil ⇒ nil ? 
    | cons p2 l2' ⇒ 
           let 〈c1,b1〉 ≝ p1 in let 〈c2,b2〉 ≝ p2 in
           match c2 with
           [ null ⇒ p1 :: merge_config l1' l2'
           | _ ⇒ p2 :: merge_config l1' l2' ] ] ].

definition R_copy0 ≝ λt1,t2.
  ∀ls,c,c0,rs,l1,l3,l4.
  t1 = midtape STape (l3@l4@〈c0,true〉::ls) 〈c,true〉 (l1@rs) → 
  no_marks l1 → no_marks (l3@l4) → |l1| = |l4| → 
  ∀l1',bv.〈c,false〉::l1 = l1'@[〈comma,bv〉] → only_bits_or_nulls l1' → 
  ∀l4',bg.l4@[〈c0,true〉] = 〈grid,bg〉::l4' → only_bits_or_nulls l4' → 
  (c = comma ∧ t2 = t1) ∨
  (c ≠ comma ∧ 
    t2 = midtape ? (reverse ? l1'@l3@〈grid,true〉::
                  merge_config l4' (reverse ? l1')@ls) 
     〈comma,true〉 rs).

axiom sem_copy0 : Realize ? copy0 R_copy0.

definition copy ≝ 
  seq STape (move_l …) (seq ? (adv_to_mark_l … (is_marked ?))
   (seq ? (clear_mark …) (seq ? (adv_to_mark_r … (is_marked ?)) (clear_mark …)))).

definition R_copy ≝ λt1,t2.
  ∀ls,c,c0,rs,l1,l3,l4.
  t1 = midtape STape (l3@〈grid,false〉::l4@〈c0,true〉::ls) 〈c,true〉 (l1@〈comma,false〉::rs) → 
  no_marks l1 → no_marks l3 → no_marks l4 → |l1| = |l4| → 
  only_bits_or_nulls (〈c0,true〉::l4) → only_bits_or_nulls (〈c,true〉::l1) → 
  t2 = midtape STape (reverse ? l1@l3@〈grid,false〉::
          merge_config (l4@[〈c0,false〉]) (reverse ? (〈c,false〉::l1))@ls) 
     〈comma,false〉 rs.
     
axiom sem_copy : Realize ? copy R_copy.

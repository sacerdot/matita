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
    ∀ls,x,rs.t1 = midtape (FinProd … alpha FinBool) ls 〈x,true〉 rs → 
    (x = c ∧
     ∀a,l1,x0,a0,l2,l3. (∀c.memb ? c l1 = true → is_marked ? c = false) → 
     ls = l1@〈a0,false〉::〈x0,true〉::l2 → 
     rs = 〈a,false〉::l3 → 
     t2 = midtape ? (〈x,false〉::l1@〈a0,true〉::〈x,false〉::l2) 〈a,true〉 l3) ∨
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
else nop
*)

definition copy_step ≝
  ifTM ? (test_char STape (λc.is_bit (\fst c)))
  (single_finalTM ? (copy_step_subcase FSUnialpha (bit false)
    (copy_step_subcase FSUnialpha (bit true) (nop ?))))
  (nop ?)
  tc_true.
  
definition R_copy_step_true ≝ 
  λt1,t2.
    ∀ls,c,rs.t1 = midtape (FinProd … FSUnialpha FinBool) ls 〈c,true〉 rs → 
    ∃x. c = bit x ∧
    (∀a,l1,c0,a0,l2,l3. (∀y.memb ? y l1 = true → is_marked ? y = false) → 
     ls = l1@〈a0,false〉::〈c0,true〉::l2 → 
     rs = 〈a,false〉::l3 → 
     t2 = midtape STape (〈bit x,false〉::l1@〈a0,true〉::〈bit x,false〉::l2) 〈a,true〉 l3).

definition R_copy_step_false ≝ 
  λt1,t2.
   ∀ls,c,rs.t1 = midtape (FinProd … FSUnialpha FinBool) ls c rs → 
   is_bit (\fst c) = false ∧ t2 = t1.

axiom sem_comp_step : 
  accRealize ? copy_step (inr … (inl … (inr … 0))) R_copy_step_true R_copy_step_false.
   
definition copy ≝ whileTM ? copy_step (inr … (inl … (inr … 0))).

definition R_copy ≝ λt1,t2.
  ∀ls,c,rs. ∀l1,d,l2,l3,l4,l5,c0.
  t1 = midtape ? ls 〈c,true〉 rs → 
  (* l1 è la stringa sorgente da copiare, l4@〈c0,true〉 è la sua destinazione *)
  〈c,false〉::rs = l1@〈d,false〉::l2 → only_bits l1 → is_bit d = false → 
   ls = l3@l4@〈c0,true〉::l5 → |l4@[〈c0,true〉]| = |l1| → 
   no_marks (l3@l4) → 
  (∀l4',d'.l4@[〈c0,false〉] = 〈d',false〉::l4' → 
   t2 = midtape STape (reverse ? l1@l3@〈d',true〉::l4'@l5) 〈d,true〉 l2).
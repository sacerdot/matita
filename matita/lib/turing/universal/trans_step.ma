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


include "turing/universal/trans_to_tuples.ma".

check TM

(* definition zero : ∀n.initN n ≝ λn.mk_Sig ?? 0 (le_O_n n). *)

definition normalTM ≝ λn,t,h. 
  λk:0<n.mk_TM FinBool (initN n) t (mk_Sig ?? 0 k) h.

definition low_config: ∀n,h,t.config FinBool (initN n) → tape STape ≝ 
λn,h.λtrans:trans_source n →trans_target n.λc.
  let q ≝ cstate … c in
  let q_low ≝  m_bits_of_state n h q in 
  let current_low ≝
    match current … (ctape … c) with
    [ None ⇒ 〈null,false〉
    | Some b ⇒ 〈bit b,false〉] in
  let low_left ≝ map … (λb.〈bit b,false〉) (left … (ctape …c)) in
  let low_right ≝ map … (λb.〈bit b,false〉) (right … (ctape …c)) in
  let table ≝ flatten ? (tuples_of_pairs n h (graph_enum ?? trans)) in
  mk_tape STape low_left (Some ? 〈grid,false〉) 
    (q_low@current_low::〈grid,false〉::table@〈grid,false〉::low_right).
  
(*
definition R_uni_step_true ≝ λt1,t2.
  ∀n,t0,table,s0,s1,c0,c1,ls,rs,curconfig,newconfig,mv.
  table_TM (S n) (〈t0,false〉::table) → 
  match_in_table (S n) (〈s0,false〉::curconfig) 〈c0,false〉
    (〈s1,false〉::newconfig) 〈c1,false〉 〈mv,false〉 (〈t0,false〉::table) → 
  legal_tape ls 〈c0,false〉 rs → 
  t1 = midtape STape (〈grid,false〉::ls) 〈s0,false〉 
    (curconfig@〈c0,false〉::〈grid,false〉::〈t0,false〉::table@〈grid,false〉::rs) → 
  ∀t1'.t1' = lift_tape ls 〈c0,false〉 rs → 
  s0 = bit false ∧
  ∃ls1,rs1,c2.
  (t2 = midtape STape (〈grid,false〉::ls1) 〈s1,false〉 
    (newconfig@〈c2,false〉::〈grid,false〉::〈t0,false〉::table@〈grid,false〉::rs1) ∧
   lift_tape ls1 〈c2,false〉 rs1 = 
   tape_move STape t1' (map_move c1 mv) ∧ legal_tape ls1 〈c2,false〉 rs1).
 *)
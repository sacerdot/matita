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
include "turing/universal/uni_step.ma".

(* definition zero : ∀n.initN n ≝ λn.mk_Sig ?? 0 (le_O_n n). *)

record normalTM : Type[0] ≝ 
{ no_states : nat;
  pos_no_states : (0 < no_states); 
  ntrans : trans_source no_states → trans_target no_states;
  nhalt : initN no_states → bool
}.

definition normalTM_to_TM ≝ λM:normalTM.
  mk_TM FinBool (initN (no_states M)) 
   (ntrans M) (mk_Sig ?? 0 (pos_no_states M)) (nhalt M).

coercion normalTM_to_TM.

definition nconfig ≝ λn. config FinBool (initN n).

(* 
definition normalTM ≝ λn,t,h. 
  λk:0<n.mk_TM FinBool (initN n) t (mk_Sig ?? 0 k) h. *)

definition low_config: ∀M:normalTM.nconfig (no_states M) → tape STape ≝ 
λM:normalTM.λc.
  let n ≝ no_states M in
  let h ≝ nhalt M in
  let t ≝ntrans M in 
  let q ≝ cstate … c in
  let q_low ≝  m_bits_of_state n h q in 
  let current_low ≝ match current … (ctape … c) with [ None ⇒ null | Some b ⇒ bit b] in
  let low_left ≝ map … (λb.〈bit b,false〉) (left … (ctape …c)) in
  let low_right ≝ map … (λb.〈bit b,false〉) (right … (ctape …c)) in
  let table ≝ flatten ? (tuples_of_pairs n h (graph_enum ?? t)) in
  let right ≝ q_low@〈current_low,false〉::〈grid,false〉::table@〈grid,false〉::low_right in
  mk_tape STape (〈grid,false〉::low_left) (option_hd … right) (tail … right).
  
lemma low_config_eq: ∀t,M,c. t = low_config M c → 
  ∃low_left,low_right,table,q_low_hd,q_low_tl,c_low.
  low_left = map … (λb.〈bit b,false〉) (left … (ctape …c)) ∧
  low_right = map … (λb.〈bit b,false〉) (right … (ctape …c)) ∧
  table = flatten ? (tuples_of_pairs (no_states M) (nhalt M) (graph_enum ?? (ntrans M))) ∧
  〈q_low_hd,false〉::q_low_tl = m_bits_of_state (no_states M) (nhalt M) (cstate … c) ∧
  c_low =  match current … (ctape … c) with [ None ⇒ null| Some b ⇒ bit b] ∧
  t = midtape STape (〈grid,false〉::low_left) 〈q_low_hd,false〉 (q_low_tl@〈c_low,false〉::〈grid,false〉::table@〈grid,false〉::low_right).
#t #M #c #eqt
  @(ex_intro … (map … (λb.〈bit b,false〉) (left … (ctape …c))))
  @(ex_intro … (map … (λb.〈bit b,false〉) (right … (ctape …c))))
  @(ex_intro … (flatten ? (tuples_of_pairs (no_states M) (nhalt M) (graph_enum ?? (ntrans M)))))
  @(ex_intro … (\fst (hd ? (m_bits_of_state (no_states M) (nhalt M) (cstate … c)) 〈bit true,false〉)))
  @(ex_intro … (tail ? (m_bits_of_state (no_states M) (nhalt M) (cstate … c))))
  @(ex_intro … (match current … (ctape … c) with [ None ⇒ null| Some b ⇒ bit b]))
% [% [% [% [% // | // ] | // ] | // ] | >eqt //]
qed.

definition low_step_R_true ≝ λt1,t2.
  ∀M:normalTM.
  ∀c: nconfig (no_states M). 
    t1 = low_config M c →
    halt ? M (cstate … c) = false ∧
      t2 = low_config M (step ? M c).

lemma unistep_to_low_step: ∀t1,t2.
  R_uni_step_true t1 t2 → low_step_R_true t1 t2.
#t1 #t2 (* whd in ⊢ (%→%); *) #Huni_step #M #c #eqt1
cases (low_config_eq … eqt1) 
#low_left * #low_right * #table * #q_low_hd * #q_low_tl * #current_low
***** #Hlow_left #Hlow_right #Htable #Hq_low #Hcurrent_low #Ht1
lapply (Huni_step ??????????????? Ht1)
whd in match (low_config M c);

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
   
    
definition low_step_R_false ≝ λt1,t2.
  ∀M:normalTM.
  ∀c: nconfig (no_states M).  
    t1 = low_config M c → halt ? M (cstate … c) = true  ∧ t1 = t2.

definition low_R ≝ λM,qstart,R,t1,t2.
    ∀tape1. t1 = low_config M (mk_config ?? qstart tape1) → 
    ∃q,tape2.R tape1 tape2 ∧
    halt ? M q = true ∧ t2 = low_config M (mk_config ?? q tape2).

definition R_TM ≝ λsig.λM:TM sig.λq.λt1,t2.
∃i,outc.
  loop ? i (step sig M) (λc.halt sig M (cstate ?? c)) (mk_config ?? q t1) = Some ? outc ∧ 
  t2 = (ctape ?? outc).

(*
definition universal_R ≝ λM,R,t1,t2. 
    Realize ? M R →    
    ∀tape1,tape2.
    R tape1 tape 2 ∧
    t1 = low_config M (initc ? M tape1) ∧
    ∃q.halt ? M q = true → t2 = low_config M (mk_config ?? q tape2).*)

axiom uni_step: TM STape.
axiom us_acc: states ? uni_step.

axiom sem_uni_step: accRealize ? uni_step us_acc low_step_R_true low_step_R_false.

definition universalTM ≝ whileTM ? uni_step us_acc.

theorem sem_universal: ∀M:normalTM. ∀qstart.
  WRealize ? universalTM (low_R M qstart (R_TM FinBool M qstart)).
#M #q #intape #i #outc #Hloop
lapply (sem_while … sem_uni_step intape i outc Hloop)
  [@daemon] -Hloop 
* #ta * #Hstar generalize in match q; -q 
@(star_ind_l ??????? Hstar)
  [#tb #q0 whd in ⊢ (%→?); #Htb #tape1 #Htb1
   cases (Htb … Htb1) -Htb #Hhalt #Htb
   <Htb >Htb1 @ex_intro 
   [|%{tape1} %
     [ % 
       [ whd @(ex_intro … 1) @(ex_intro … (mk_config … q0 tape1))
        % [|%] whd in ⊢ (??%?); >Hhalt % 
       | @Hhalt ]
     | % ]
   ]
  |#tb #tc #td whd in ⊢ (%→?); #Htc #Hstar1 #IH 
   #q #Htd #tape1 #Htb 
   lapply (IH (\fst (trans ? M 〈q,current ? tape1〉)) Htd) -IH 
   #IH cases (Htc … Htb); -Htc #Hhaltq 
   whd in match (step ???); >(eq_pair_fst_snd ?? (trans ???)) 
   #Htc change with (mk_config ????) in Htc:(???(??%)); 
   cases (IH ? Htc) #q1 * #tape2 * * #HRTM #Hhaltq1 #Houtc
   @(ex_intro … q1) @(ex_intro … tape2) % 
    [%
      [cases HRTM #k * #outc1 * #Hloop #Houtc1
       @(ex_intro … (S k)) @(ex_intro … outc1) % 
        [>loop_S_false [2://] whd in match (step ???); 
         >(eq_pair_fst_snd ?? (trans ???)) @Hloop
        |@Houtc1
        ]
      |@Hhaltq1]
    |@Houtc
    ]
  ]
qed.

lemma R_TM_to_R: ∀sig,M,R. ∀t1,t2. 
  WRealize sig M R → R_TM ? M (start ? M) t1 t2 → R t1 t2.
#sig #M #R #t1 #t2 whd in ⊢ (%→?); #HMR * #i * #outc *
#Hloop #Ht2 >Ht2 @(HMR … Hloop)
qed.

axiom WRealize_to_WRealize: ∀sig,M,R1,R2.
  (∀t1,t2.R1 t1 t2 → R2 t1 t2) → WRealize sig M R1 → WRealize ? M R2.

theorem sem_universal2: ∀M:normalTM. ∀R.
  WRealize ? M R → WRealize ? universalTM (low_R M (start ? M) R).
#M #R #HMR lapply (sem_universal … M (start ? M)) @WRealize_to_WRealize
#t1 #t2 whd in ⊢ (%→%); #H #tape1 #Htape1 cases (H ? Htape1)
#q * #tape2 * * #HRTM #Hhalt #Ht2 @(ex_intro … q) @(ex_intro … tape2)
% [% [@(R_TM_to_R … HRTM) @HMR | //] | //]
qed.
 

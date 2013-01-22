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

include "turing/simple_machines.ma".
include "turing/multi_universal/unistep_aux.ma".

axiom sem_unistep: ∀M. unistep ⊨ R_unistep_high M.

definition stop ≝ λc.
  match c with [ bit b ⇒ notb b | _ ⇒ true].
  
definition uni_body ≝ 
  ifTM ?? (mtestR ? cfg 2 stop)
    (single_finalTM ?? unistep)
    (nop …) (mtestR_acc ? cfg 2 stop).

definition acc_body : states ?? uni_body ≝ (inr … (inl … (inr … start_nop))).

definition ub_R_true ≝ λM,t1,t2.
  ∀c: nconfig (no_states M). 
  t1=low_tapes M c→
    t2=low_tapes M (step FinBool M c) ∧ halt ? M (cstate … c) = false.
  
definition ub_R_false ≝ λM,t1,t2.
  ∀c: nconfig (no_states M).  
  t1 = low_tapes M c → t1 = t2 ∧ halt ? M (cstate … c) = true.

lemma sem_uni_body: ∀M.
  uni_body ⊨ [acc_body: ub_R_true M, ub_R_false M].
#M #cf 
@(acc_sem_if_app ????????????
   (sem_mtestR ? cfg 2 stop (le_S ?? (le_n 1)))
   (sem_unistep M)
   (sem_nop …))
[#t1 #t2 #t3 whd in ⊢ (%→?); #Htest #Ht2 * #q #Mt #Ht1
 >Ht1 in Htest; >cfg_low_tapes whd in match (bits_of_state ???);
 #Htest lapply (Htest … (refl ??)) * <Ht1 #Ht3 #Hstop >Ht3 in Ht2;
 #Ht2 % [@Ht2 //] lapply Hstop  whd in match (nhalt ??); 
 cases (nhalt M q) whd in match (stop ?); * /2/
|#t1 #t2 #t3 whd in ⊢ (%→?); #Htest #Hnop >Hnop -Hnop * #q #Mt #Ht1 >Ht1 in Htest;
 >cfg_low_tapes whd in match (bits_of_state ???); 
 #Htest lapply (Htest … (refl ??)) whd in match (nhalt ??); 
 cases (nhalt M q) whd in match (stop ?); * /2/ 
]
qed.

definition universalTM ≝ whileTM ?? uni_body acc_body.

definition low_R ≝ λM,q,R.λt1,t2:Vector (tape FSUnialpha) 3.
    ∀Mt. t1 = low_tapes M (mk_config ?? q Mt) → 
    ∃cout. R Mt (ctape … cout) ∧
    halt ? M (cstate … cout) = true ∧ t2 = low_tapes M cout.

theorem sem_universal: ∀M:normalTM. ∀q.
  universalTM ⊫ low_R M q (R_TM FinBool M q).
#M #q #intape #i #outc #Hloop
lapply (sem_while … (sem_uni_body M … ) intape i outc Hloop) [%] -Hloop 
* #ta * #Hstar lapply q -q @(star_ind_l ??????? Hstar) -Hstar
  [#q whd in ⊢ (%→?); #HFalse whd #Mt #Hta 
   lapply (HFalse … Hta) * #Hta1 #Hhalt %{(mk_config ?? q Mt)} %
    [%[%{1} %{(mk_config ?? q Mt)} % // whd in ⊢ (??%?); >Hhalt % |@Hhalt]
    |<Hta1 @Hta  
    ]
  |#t1 #t2 whd in ⊢ (%→?); #Hstep #Hstar #IH #q #Hta whd #Mt #Ht1
   lapply (Hstep … Ht1) * -Hstep #Ht2 #Hhalt
   lapply(IH (cstate … (step FinBool M (mk_config ?? q Mt))) Hta ??) [@Ht2|skip] -IH 
   * #cout * * #HRTM #Hhalt1 #Houtc
   %{cout} 
   %[%[cases HRTM #k * #outc1 * <config_expand #Hloop #Houtc1
       %{(S k)} %{outc1} % 
        [whd in ⊢ (??%?); >Hhalt whd in ⊢ (??%?); @Hloop 
        |@Houtc1
        ]
      |@Hhalt1]
    |@Houtc
    ]
  ] 
qed.
  
theorem sem_universal2: ∀M:normalTM. ∀R.
  M ⊫ R → universalTM ⊫ (low_R M (start ? M) R).
#M #R #HMR lapply (sem_universal … M (start ? M)) @WRealize_to_WRealize
#t1 #t2 whd in ⊢ (%→%); #H #tape1 #Htape1 cases (H ? Htape1)
#c * * #HRTM #Hhalt #Ht2 %{c}
% [% [@(R_TM_to_R … HRTM) @HMR | //] | //]
qed.
 
axiom terminate_UTM: ∀M:normalTM.∀t. 
  M ↓ t → universalTM ↓ (low_tapes M (mk_config ?? (start ? M) t)).
 







lemma current_embedding: ∀c.
  high_c (〈match c with [None ⇒ null | Some b ⇒ bit b],false〉) = c.
  * normalize // qed.

lemma tape_embedding: ∀ls,c,rs.
 high_tape 
   (map ?? (λb.〈bit b,false〉) ls) 
   (〈match c with [None ⇒ null | Some b ⇒ bit b],false〉)
   (map ?? (λb.〈bit b,false〉) rs) = mk_tape ? ls c rs.
#ls #c #rs >high_tape_eq >bool_embedding >bool_embedding
>current_embedding %
qed.

definition high_move ≝ λc,mv.
  match c with 
  [ bit b ⇒ Some ? 〈b,move_of_unialpha mv〉
  | _ ⇒ None ?
  ].

definition map_move ≝ 
  λc,mv.match c with [ null ⇒ None ? | _ ⇒ Some ? 〈c,false,move_of_unialpha mv〉 ].

definition low_step_R_true ≝ λt1,t2.
  ∀M:normalTM.
  ∀c: nconfig (no_states M). 
    t1 = low_config M c →
    halt ? M (cstate … c) = false ∧
      t2 = low_config M (step ? M c).

definition low_tape_aux : ∀M:normalTM.tape FinBool → tape STape ≝ 
λM:normalTM.λt.
  let current_low ≝ match current … t with 
    [ None ⇒ None ? | Some b ⇒ Some ? 〈bit b,false〉] in
  let low_left ≝ map … (λb.〈bit b,false〉) (left … t) in
  let low_right ≝ map … (λb.〈bit b,false〉) (right … t) in
  mk_tape STape low_left current_low low_right. 

lemma left_of_low_tape: ∀M,t. 
  left ? (low_tape_aux M t) = map … (λb.〈bit b,false〉) (left … t).
#M * //
qed. 

lemma right_of_low_tape: ∀M,t. 
  right ? (low_tape_aux M t) = map … (λb.〈bit b,false〉) (right … t).
#M * //
qed. 

definition low_move ≝ λaction:option (bool × move).
  match action with
  [None ⇒ None ?
  |Some act ⇒ Some ? (〈〈bit (\fst act),false〉,\snd act〉)].

(* simulation lemma *)
lemma low_tape_move : ∀M,action,t.
  tape_move STape (low_tape_aux M t) (low_move action) =
  low_tape_aux M (tape_move FinBool t action). 
#M * // (* None *)
* #b #mv #t cases mv cases t //
  [#ls #c #rs cases ls //|#ls #c #rs cases rs //]
qed.

lemma left_of_lift: ∀ls,c,rs. left ? (lift_tape ls c rs) = ls.
#ls * #c #b #rs cases c // cases ls // cases rs //
qed.

lemma right_of_lift: ∀ls,c,rs. legal_tape ls c rs →
  right ? (lift_tape ls c rs) = rs.
#ls * #c #b #rs * #_ cases c // cases ls cases rs // #a #tll #b #tlr
#H @False_ind cases H [* [#H1 /2/ |#H1 destruct] |#H1 destruct]
qed.


lemma current_of_lift: ∀ls,c,b,rs. legal_tape ls 〈c,b〉 rs →
  current STape (lift_tape ls 〈c,b〉 rs) =
    match c with [null ⇒ None ? | _ ⇒ Some ? 〈c,b〉].
#ls #c #b #rs cases c // whd in ⊢ (%→?); * #_ 
* [* [#Hnull @False_ind /2/ | #Hls >Hls whd in ⊢ (??%%); cases rs //]
  |#Hrs >Hrs whd in ⊢ (??%%); cases ls //]
qed.

lemma current_of_lift_None: ∀ls,c,b,rs. legal_tape ls 〈c,b〉 rs →
  current STape (lift_tape ls 〈c,b〉 rs) = None ? →
    c = null.
#ls #c #b #rs #Hlegal >(current_of_lift … Hlegal) cases c normalize  
  [#b #H destruct |// |3,4,5:#H destruct ]
qed.

lemma current_of_lift_Some: ∀ls,c,c1,rs. legal_tape ls c rs →
  current STape (lift_tape ls c rs) = Some ? c1 →
    c = c1.
#ls * #c #cb #b #rs #Hlegal >(current_of_lift … Hlegal) cases c normalize 
 [#b1 #H destruct // |#H destruct |3,4,5:#H destruct //]
qed.

lemma current_of_low_None: ∀M,t. current FinBool t = None ? → 
  current STape (low_tape_aux M t) = None ?.
#M #t cases t // #l #b #r whd in ⊢ ((??%?)→?); #H destruct
qed.
  
lemma current_of_low_Some: ∀M,t,b. current FinBool t = Some ? b → 
  current STape (low_tape_aux M t) = Some ? 〈bit b,false〉.
#M #t cases t 
  [#b whd in ⊢ ((??%?)→?); #H destruct
  |#b #l #b1 whd in ⊢ ((??%?)→?); #H destruct
  |#b #l #b1 whd in ⊢ ((??%?)→?); #H destruct
  |#c #c1 #l #r whd in ⊢ ((??%?)→?); #H destruct %
  ]
qed.

lemma current_of_low:∀M,tape,ls,c,rs. legal_tape ls c rs → 
  lift_tape ls c rs = low_tape_aux M tape →
  c = 〈match current … tape  with 
       [ None ⇒ null | Some b ⇒ bit b], false〉.
#M #tape #ls * #c #cb #rs #Hlegal #Hlift  
cut (current ? (lift_tape ls 〈c,cb〉 rs) = current ? (low_tape_aux M tape))
  [@eq_f @Hlift] -Hlift #Hlift
cut (current … tape = None ? ∨ ∃b.current … tape = Some ? b)
  [cases (current … tape) [%1 // | #b1 %2 /2/ ]] *  
  [#Hcurrent >Hcurrent normalize
   >(current_of_low_None …Hcurrent) in Hlift; #Hlift 
   >(current_of_lift_None … Hlegal Hlift) 
   @eq_f cases Hlegal * * #Hmarks #_ #_ #_ @(Hmarks 〈c,cb〉) @memb_hd
  |* #b #Hcurrent >Hcurrent normalize
   >(current_of_low_Some …Hcurrent) in Hlift; #Hlift 
   @(current_of_lift_Some … Hlegal Hlift) 
  ]
qed.

(*
lemma current_of_low:∀M,tape,ls,c,rs. legal_tape ls c rs → 
  lift_tape ls c rs = low_tape_aux M tape →
  c = 〈match current … tape  with 
       [ None ⇒ null | Some b ⇒ bit b], false〉.
#M #tape #ls * #c #cb #rs * * #_ #H cases (orb_true_l … H)
  [cases c [2,3,4,5: whd in ⊢ ((??%?)→?); #Hfalse destruct]
   #b #_ #_ cases tape 
    [whd in ⊢ ((??%%)→?); #H destruct
    |#a #l whd in ⊢ ((??%%)→?); #H destruct 
    |#a #l whd in ⊢ ((??%%)→?); #H destruct 
    |#a #l #r whd in ⊢ ((??%%)→?); #H destruct //
    ]
  |cases c 
    [#b whd in ⊢ ((??%?)→?); #Hfalse destruct
    |3,4,5:whd in ⊢ ((??%?)→?); #Hfalse destruct]
   #_ * [* [#Habs @False_ind /2/
           |#Hls >Hls whd in ⊢ ((??%%)→?); *)
          
    
(* sufficent conditions to have a low_level_config *)
lemma is_low_config: ∀ls,c,rs,M,s,tape,qhd,q_tl,table.
legal_tape ls c rs →
table = flatten ? (tuples_list (no_states M) (nhalt M) (graph_enum ?? (ntrans M))) →
lift_tape ls c rs = low_tape_aux M tape →
〈qhd,false〉::q_tl = m_bits_of_state (no_states M) (nhalt M) s →
midtape STape (〈grid,false〉::ls) 
  〈qhd,false〉 
  (q_tl@c::〈grid,false〉::table@〈grid,false〉::rs) = 
  low_config M (mk_config ?? s tape).
#ls #c #rs #M #s #tape #qhd #q_tl #table #Hlegal #Htable
#Hlift #Hstate whd in match (low_config ??); <Hstate 
@eq_f3 
  [@eq_f <(left_of_lift ls c rs) >Hlift //
  | cut (∀A.∀a,b:A.∀l1,l2. a::l1 = b::l2 → a=b)
    [#A #a #b #l1 #l2 #H destruct (H) %] #Hcut
   @(Hcut …Hstate)
  |@eq_f <(current_of_low … Hlegal Hlift) @eq_f @eq_f <Htable @eq_f @eq_f
   <(right_of_lift ls c rs Hlegal) >Hlift @right_of_low_tape
  ]
qed.

lemma unistep_true_to_low_step: ∀t1,t2.
  R_uni_step_true t1 t2 → low_step_R_true t1 t2.
#t1 #t2 (* whd in ⊢ (%→%); *) #Huni_step * #n #posn #t #h * #qin #tape #eqt1
cases (low_config_eq … eqt1) 
#low_left * #low_right * #table * #q_low_hd * #q_low_tl * #current_low
***** #Hlow_left #Hlow_right #Htable #Hq_low #Hcurrent_low #Ht1
letin trg ≝ (t 〈qin,current ? tape〉)
letin qout_low ≝ (m_bits_of_state n h (\fst trg))
letin qout_low_hd ≝ (hd ? qout_low 〈bit true,false〉)
letin qout_low_tl ≝ (tail ? qout_low)
letin low_act ≝ (low_action (\snd (t 〈qin,current ? tape〉)))
letin low_cout ≝ (\fst low_act)
letin low_m ≝ (\snd low_act)
lapply (Huni_step n table q_low_hd (\fst qout_low_hd) 
       current_low low_cout low_left low_right q_low_tl qout_low_tl low_m … Ht1) 
  [@daemon
  |>Htable
   @(trans_to_match n h t 〈qin,current ? tape〉 … (refl …))
   >Hq_low  >Hcurrent_low whd in match (mk_tuple ?????);
   >(eq_pair_fst_snd … (t …)) whd in ⊢ (??%?);
   >(eq_pair_fst_snd … (low_action …)) %
  |//
  |@daemon
  ]
-Ht1 #Huni_step lapply (Huni_step ? (refl …)) -Huni_step *
#q_low_head_false * #ls1 * #rs1 * #c2 * * 
#Ht2 #Hlift #Hlegal %
  [whd in ⊢ (??%?); >q_low_head_false in Hq_low; 
   whd in ⊢ ((???%)→?); generalize in match (h qin);
   #x #H destruct (H) %
  |>Ht2 whd in match (step FinBool ??); 
   whd in match (trans ???); 
   >(eq_pair_fst_snd … (t ?))
   @is_low_config // >Hlift
   <low_tape_move @eq_f2
    [>Hlow_left >Hlow_right >Hcurrent_low whd in ⊢ (??%%); 
     cases (current …tape) [%] #b whd in ⊢ (??%%); %
    |whd in match low_cout; whd in match low_m; whd in match low_act; 
     generalize in match (\snd (t ?)); * [%] * #b #mv
     whd in  ⊢ (??(?(???%)?)%); cases mv % 
    ]
  ]
qed.

definition low_step_R_false ≝ λt1,t2.
  ∀M:normalTM.
  ∀c: nconfig (no_states M).  
    t1 = low_config M c → halt ? M (cstate … c) = true  ∧ t1 = t2.

lemma unistep_false_to_low_step: ∀t1,t2.
  R_uni_step_false t1 t2 → low_step_R_false t1 t2.
#t1 #t2 (* whd in ⊢ (%→%); *) #Huni_step * #n #posn #t #h * #qin #tape #eqt1
cases (low_config_eq … eqt1) #low_left * #low_right * #table * #q_low_hd * #q_low_tl * #current_low
***** #_ #_ #_ #Hqin #_ #Ht1 whd in match (halt ???);
cases (Huni_step (h qin) ?) [/2/] >Ht1 whd in ⊢ (??%?); @eq_f
normalize in Hqin; destruct (Hqin) %
qed.

definition low_R ≝ λM,qstart,R,t1,t2.
    ∀tape1. t1 = low_config M (mk_config ?? qstart tape1) → 
    ∃q,tape2.R tape1 tape2 ∧
    halt ? M q = true ∧ t2 = low_config M (mk_config ?? q tape2).

lemma sem_uni_step1: 
  uni_step ⊨ [us_acc: low_step_R_true, low_step_R_false].
qed. 

definition universalTM ≝ whileTM ? uni_step us_acc.

theorem sem_universal: ∀M:normalTM. ∀qstart.
  universalTM ⊫ (low_R M qstart (R_TM FinBool M qstart)).
qed.

theorem sem_universal2: ∀M:normalTM. ∀R.
  M ⊫ R → universalTM ⊫ (low_R M (start ? M) R).
#M #R #HMR lapply (sem_universal … M (start ? M)) @WRealize_to_WRealize
#t1 #t2 whd in ⊢ (%→%); #H #tape1 #Htape1 cases (H ? Htape1)
#q * #tape2 * * #HRTM #Hhalt #Ht2 @(ex_intro … q) @(ex_intro … tape2)
% [% [@(R_TM_to_R … HRTM) @HMR | //] | //]
qed.
 
axiom terminate_UTM: ∀M:normalTM.∀t. 
  M ↓ t → universalTM ↓ (low_config M (mk_config ?? (start ? M) t)).
 

include "turing/basic_machines.ma".
include "turing/if_machine.ma".
include "turing/auxiliary_machines1.ma".
include "turing/multi_to_mono/trace_alphabet.ma".

(* a machine that moves the i trace r: we reach the left margin of the i-trace 
and make a (shifted) copy of the old tape up to the end of the right margin of 
the i-trace. Then come back to the origin. *)

definition shift_i ≝ λsig,n,i.λa,b:Vector (sig_ext sig) n.
  change_vec (sig_ext sig) n a (nth i ? b (blank ?)) i.

(* vec is a coercion. Why should I insert it? *)
definition mti_step ≝ λsig:FinSet.λn,i.
  ifTM (multi_sig sig n) (test_char ? (λc:multi_sig sig n.¬(nth i ? (vec … c) (blank ?))==blank ?))
     (single_finalTM … (ncombf_r (multi_sig sig n) (shift_i sig n i) (all_blank sig n)))
     (nop ?) tc_true.
      
definition Rmti_step_true ≝ 
λsig,n,i,t1,t2. 
  ∃b:multi_sig sig n. (nth i ? (vec … b) (blank ?) ≠ blank ?) ∧
    ((∃ls,a,rs.
       t1 = midtape (multi_sig sig n) ls b (a::rs) ∧
       t2 = midtape (multi_sig sig n) ((shift_i sig n i b a)::ls) a rs) ∨
     (∃ls.
       t1 = midtape ? ls b [] ∧
       t2 = rightof ? (shift_i sig n i b (all_blank sig n)) ls)).

(* 〈combf0,all_blank sig n〉 *)
definition Rmti_step_false ≝ 
  λsig,n,i,t1,t2.
    (∀ls,b,rs. t1 = midtape (multi_sig sig n) ls b rs →
     (nth i ? (vec … b) (blank ?) = blank ?)) ∧ t2 = t1.

lemma sem_mti_step :
  ∀sig,n,i.
  mti_step sig n i  ⊨ 
    [inr … (inl … (inr … start_nop)): Rmti_step_true sig n i, Rmti_step_false sig n i].
#sig #n #i
@(acc_sem_if_app (multi_sig sig n) ?????????? 
     (sem_test_char …) (sem_ncombf_r (multi_sig sig n) (shift_i sig n i)(all_blank sig n)) 
     (sem_nop (multi_sig sig n)))
  [#intape #outtape #tapea whd in ⊢ (%→%→%); * * #c *
   #Hcur cases (current_to_midtape … Hcur) #ls * #rs #Hintape
   #ctest #Htapea * #Hout1 #Hout2 @(ex_intro … c) %
    [@(\Pf (injective_notb … )) @ctest]
   generalize in match Hintape; -Hintape cases rs
    [#Hintape %2 @(ex_intro …ls) % // @Hout1 >Htapea @Hintape
    |#a #rs1 #Hintape %1
     @(ex_intro … ls) @(ex_intro … a) @(ex_intro … rs1) % //
     @Hout2 >Htapea @Hintape
    ]
  |#intape #outtape #tapea whd in ⊢ (%→%→%);
   * #Htest #tapea #outtape 
   % // #ls #b #rs
   #intape lapply (Htest b ?) [>intape //] -Htest #Htest 
   lapply (injective_notb ? true Htest) -Htest #Htest @(\P Htest) 
  ]   
qed.
      
(* move tape i machine *)
definition mti ≝ 
  λsig,n,i.whileTM (multi_sig sig n) (mti_step sig n i) (inr … (inl … (inr … start_nop))). 

(* v2 is obtained from v1 shifting left the i-th trace *)
definition shift_l ≝ λsig,n,i,v1,v2.  (* multi_sig sig n*) 
  |v1| = |v2| ∧ 
  ∀j.nth j ? v2 (all_blank sig n) = 
      change_vec ? n (nth j ? v1 (all_blank sig n)) 
        (nth i ? (vec … (nth (S j) ? v1 (all_blank sig n))) (blank ?)) i.
        
lemma trace_shift: ∀sig,n,i,v1,v2. i < n → 0 < |v1| →
  shift_l sig n i v1 v2 → trace ? n i v2 = tail ? (trace ? n i v1)@[blank sig].
#sig #n #i #v1 #v2 #lein #Hlen * #Hlen1 #Hnth @(nth_to_eq … (blank ?))
  [>length_trace <Hlen1 generalize in match Hlen; cases v1  
    [normalize #H @(le_n_O_elim … H) // 
    |#b #tl #_ normalize >length_append >length_trace normalize //
    ]
  |#j >nth_trace >Hnth >nth_change_vec // >tail_trace 
   cut (trace ? n i [all_blank sig n] = [blank sig]) 
     [normalize >blank_all_blank //] 
   #Hcut <Hcut <trace_append >nth_trace 
   <nth_extended //
  ]
qed.
 
lemma trace_shift_neq: ∀sig,n,i,j,v1,v2. i < n → 0 < |v1| → i ≠ j →
  shift_l sig n i v1 v2 → trace ? n j v2 = trace ? n j v1.
#sig #n #i #j #v1 #v2 #lein #Hlen #Hneq * #Hlen1 #Hnth @(nth_to_eq … (blank ?))
  [>length_trace >length_trace @sym_eq @Hlen1
  |#k >nth_trace >Hnth >nth_change_vec_neq // >nth_trace // 
  ]
qed.

axiom daemon: ∀P:Prop.P.

definition R_mti ≝ 
  λsig,n,i,t1,t2.
    (∀a,rs. t1 = rightof ? a rs → t2 = t1) ∧
    (∀a,ls,rs. 
      t1 = midtape (multi_sig sig n) ls a rs → 
      (nth i ? (vec … a) (blank ?) = blank ? ∧ t2 = t1) ∨
      ((∃rs1,b,rs2,rss.
        rs = rs1@b::rs2 ∧ 
        nth i ? (vec … b) (blank ?) = (blank ?) ∧
        (∀x. mem ? x (a::rs1) → nth i ? (vec … x) (blank ?) ≠ (blank ?)) ∧
        shift_l sig n i (a::rs1) rss ∧
        t2 = midtape (multi_sig sig n) ((reverse ? rss)@ls) b rs2) ∨
      (∃b,rss. 
        (∀x. mem ? x (a::rs) → nth i ? (vec … x) (blank ?) ≠ (blank ?)) ∧
        shift_l sig n i (a::rs) (rss@[b]) ∧
        t2 = rightof (multi_sig sig n) (shift_i sig n i b (all_blank sig n)) 
         ((reverse ? rss)@ls)))).  

lemma sem_mti:
  ∀sig,n,i.
  WRealize (multi_sig sig n) (mti sig n i) (R_mti sig n i).
#sig #n #i #inc #j #outc #Hloop
lapply (sem_while … (sem_mti_step sig n i) inc j outc Hloop) [%]
-Hloop * #t1 * #Hstar @(star_ind_l ??????? Hstar)
[ whd in ⊢ (% → ?); * #H1 #H2 % 
  [#a #rs #Htape1 @H2
  |#a #ls #rs #Htapea % % [@(H1 … Htapea) |@H2]
  ]
| #tapeb #tapec #Hstar1 #HRtrue #IH #HRfalse
  lapply (IH HRfalse) -IH -HRfalse whd in ⊢ (%→%); 
  * #IH1 #IH2 %
  [#b0 #ls #Htapeb cases Hstar1 #b * #_ *
    [* #ls0 * #a * #rs0 * >Htapeb #H destruct (H)
    |* #ls0 * >Htapeb #H destruct (H)
    ]
  |#b0 #ls #rs #Htapeb cases Hstar1 #b * #btest *
  [* #ls1 * #a * #rs1 * >Htapeb #H destruct (H) #Htapec 
   %2 cases (IH2 … Htapec)
    [(* case a = None *)
     * #testa #Hout %1
     %{[ ]} %{a} %{rs1} %{[shift_i sig n i b a]} %
      [%[%[% // |#x #Hb >(mem_single ??? Hb) // ] 
        |@daemon]
      |>Hout >reverse_single @Htapec
      ] 
    |*
      [ (* case a \= None and exists b = None *) -IH1 -IH2 #IH
        %1 cases IH -IH #rs10 * #b0 * #rs2 * #rss * * * *
        #H1 #H2 #H3 #H4 #H5
        %{(a::rs10)} %{b0} %{rs2} %{(shift_i sig n i b a::rss)}
        %[%[%[%[>H1 //|@H2]
            |#x * [#eqxa >eqxa (*?? *) @daemon|@H3]]
          |@daemon]
        |>H5 >reverse_cons >associative_append //
        ]
      | (* case a \= None and we reach the end of the (full) tape *) -IH1 -IH2 #IH
        %2 cases IH -IH #b0 * #rss * * #H1 #H2 #H3
        %{b0} %{(shift_i sig n i b a::rss)} 
        %[%[#x * [#eqxb >eqxb @btest|@H1]
           |@daemon]
        |>H3 >reverse_cons >associative_append //
        ]
      ]
    ]
  |(* b \= None but the left tape is empty *)
   * #ls0 * >Htapeb #H destruct (H) #Htapec
   %2 %2 %{b} %{[ ]} 
   %[%[#x * [#eqxb >eqxb @btest|@False_ind]
      |@daemon (*shift of  dingle char OK *)]
    |>(IH1 … Htapec) >Htapec //
    ]
  ]
qed.
    
lemma WF_mti_niltape:
  ∀sig,n,i. WF ? (inv ? (Rmti_step_true sig n i)) (niltape ?).
#sig #n #i @wf #t1 whd in ⊢ (%→?); * #b * #_ *
  [* #ls * #a * #rs * #H destruct|* #ls * #H destruct ]
qed.

lemma WF_mti_rightof:
  ∀sig,n,i,a,ls. WF ? (inv ? (Rmti_step_true sig n i)) (rightof ? a ls).
#sig #n #i #a #ls @wf #t1 whd in ⊢ (%→?); * #b * #_ *
  [* #ls * #a * #rs * #H destruct|* #ls * #H destruct ]
qed.

lemma WF_mti_leftof:
  ∀sig,n,i,a,ls. WF ? (inv ? (Rmti_step_true sig n i)) (leftof ? a ls).
#sig #n #i #a #ls @wf #t1 whd in ⊢ (%→?); * #b * #_ *
  [* #ls * #a * #rs * #H destruct|* #ls * #H destruct ]
qed.

lemma terminate_mti:
  ∀sig,n,i.∀t. Terminate ? (mti sig n i) t.
#sig #n #i #t @(terminate_while … (sem_mti_step sig n i)) [%]
cases t // #ls #c #rs lapply c -c lapply ls -ls  elim rs 
  [#ls #c @wf #t1 whd in ⊢ (%→?); * #b * #_ *
    [* #ls1 * #a * #rs1 * #H destruct
    |* #ls1 * #H destruct #Ht1 >Ht1 //
    ]
  |#a #rs1 #Hind #ls #c @wf #t1 whd in ⊢ (%→?); * #b * #_ *
    [* #ls1 * #a2 * #rs2 * #H destruct (H) #Ht1 >Ht1 //
    |* #ls1 *  #H destruct
    ]
  ]
qed.

lemma ssem_mti: ∀sig,n,i.
  Realize ? (mti sig n i) (R_mti sig n i).
/2/ qed.
   
(******************************************************************************)
(* mtiL: complete move L for tape i. We reaching the left border of trace i,  *)
(* add a blank if there is no more tape, then move the i-trace and finally    *)
(* come back to the head position.                                            *)
(******************************************************************************)

definition no_blank ≝ λsig,n,i.λc:multi_sig sig n.
  ¬(nth i ? (vec … c) (blank ?))==blank ?.

definition no_head ≝ λsig,n.λc:multi_sig sig n.
  ¬((nth n ? (vec … c) (blank ?))==head ?).

let rec to_blank sig l on l ≝
  match l with
  [ nil ⇒  [ ]
  | cons a tl ⇒ 
      if a == blank sig then [ ] else a::(to_blank sig tl)]. 
      
definition to_blank_i ≝ λsig,n,i,l. to_blank ? (trace sig n i l).

lemma to_blank_i_def : ∀sig,n,i,l. 
  to_blank_i sig n i l = to_blank ? (trace sig n i l).
// qed.
(*
  match l with
  [ nil ⇒  [ ]
  | cons a tl ⇒ 
      let ai ≝ nth i ? (vec … n a) (blank sig) in
      if ai == blank ? then [ ] else ai::(to_blank sig n i tl)]. *)

lemma to_blank_cons_b : ∀sig,n,i,a,l.
  nth i ? (vec … n a) (blank sig) = blank ? →
  to_blank_i sig n i (a::l) = [ ].
#sig #n #i #a #l #H whd in match (to_blank_i ????);
>(\b H) //
qed.      

lemma to_blank_cons_nb: ∀sig,n,i,a,l.
  nth i ? (vec … n a) (blank sig) ≠ blank ? →
  to_blank_i sig n i (a::l) = 
    nth i ? (vec … n a) (blank sig)::(to_blank_i sig n i l).
#sig #n #i #a #l #H whd in match (to_blank_i ????);
>(\bf H) //
qed.

axiom to_blank_hd : ∀sig,n,a,b,l1,l2. 
  (∀i. i ≤ n → to_blank_i sig n i (a::l1) = to_blank_i sig n i (b::l2)) → a = b.

lemma to_blank_i_ext : ∀sig,n,i,l.
  to_blank_i sig n i l = to_blank_i sig n i (l@[all_blank …]).
#sig #n #i #l elim l
  [@sym_eq @to_blank_cons_b @blank_all_blank
  |#a #tl #Hind whd in match (to_blank_i ????); >Hind <to_blank_i_def >Hind %
  ]
qed. 
  
lemma to_blank_hd_cons : ∀sig,n,i,l1,l2.
  to_blank_i sig n i (l1@l2) = 
    to_blank_i … i (l1@(hd … l2 (all_blank …))::tail … l2).
#sig #n #i #l1 #l2 cases l2
  [whd in match (hd ???); whd in match (tail ??); >append_nil @to_blank_i_ext 
  |#a #tl % 
  ]
qed.

lemma to_blank_i_chop : ∀sig,n,i,a,l1,l2.
 (nth i ? (vec … a) (blank ?))= blank ? → 
 to_blank_i sig n i (l1@a::l2) = to_blank_i sig n i l1.
#sig #n #i #a #l1 elim l1
  [#l2 #H @to_blank_cons_b //
  |#x #tl #Hind #l2 #H whd in match (to_blank_i ????); 
   >(Hind l2 H) <to_blank_i_def >(Hind l2 H) %
  ]
qed. 
    
(******************************* move_to_blank_L ******************************)
(* we compose machines together to reduce the number of output cases, and 
   improve semantics *)
   
definition move_to_blank_L ≝ λsig,n,i.
  (move_until ? L (no_blank sig n i)) · extend ? (all_blank sig n).
  
definition R_move_to_blank_L ≝ λsig,n,i,t1,t2.
(current ? t1 = None ? → 
  t2 = midtape (multi_sig sig n) (left ? t1) (all_blank …) (right ? t1)) ∧
∀ls,a,rs.t1 = midtape ? ls a rs → 
  ((no_blank sig n i a = false) ∧ t2 = t1) ∨
  (∃b,ls1,ls2.
    (no_blank sig n i b = false) ∧ 
    (∀j.j ≤n → to_blank_i ?? j (ls1@b::ls2) = to_blank_i ?? j ls) ∧
    t2 = midtape ? ls2 b ((reverse ? (a::ls1))@rs)).

definition R_move_to_blank_L_new ≝ λsig,n,i,t1,t2.
(current ? t1 = None ? → 
  t2 = midtape (multi_sig sig n) (left ? t1) (all_blank …) (right ? t1)) ∧
∀ls,a,rs.t1 = midtape ? ls a rs → 
  (∃b,ls1,ls2.
    (no_blank sig n i b = false) ∧ 
    (hd ? (ls1@[b]) (all_blank …) = a) ∧ (* not implied by the next fact *)
    (∀j.j ≤n → to_blank_i ?? j (ls1@b::ls2) = to_blank_i ?? j (a::ls)) ∧
    t2 = midtape ? ls2 b ((reverse ? ls1)@rs)).
    
theorem sem_move_to_blank_L: ∀sig,n,i. 
  move_to_blank_L sig n i  ⊨ R_move_to_blank_L sig n i.
#sig #n #i 
@(sem_seq_app ?????? 
  (ssem_move_until_L ? (no_blank sig n i)) (sem_extend ? (all_blank sig n)))
#tin #tout * #t1 * * #Ht1a #Ht1b * #Ht2a #Ht2b %
  [#Hcur >(Ht1a Hcur) in Ht2a; /2 by /
  |#ls #a #rs #Htin -Ht1a cases (Ht1b … Htin)
    [* #Hnb #Ht1 -Ht1b -Ht2a >Ht1 in Ht2b; >Htin #H %1 
     % [//|@H normalize % #H1 destruct (H1)] 
    |* 
    [(* we find the blank *)
     * #ls1 * #b * #ls2 * * * #H1 #H2 #H3 #H4 %2
     %{b} %{ls1} %{ls2} 
     %[%[@H2|>H1 //] 
      |-Ht1b -Ht2a >H4 in Ht2b; #H5 @H5
       % normalize #H6 destruct (H6)
      ]
    |* #b * #lss * * #H1 #H2 #H3 %2
     %{(all_blank …)} %{ls} %{[ ]} 
     %[%[whd in match (no_blank ????); >blank_all_blank // @daemon
        |@daemon (* make a lemma *)] 
      |-Ht1b -Ht2b >H3 in Ht2a; 
       whd in match (left ??); whd in match (right ??); #H4
       >H2 >reverse_append >reverse_single @H4 normalize // 
      ]
    ]
  ]
qed.

theorem sem_move_to_blank_L_new: ∀sig,n,i. 
  move_to_blank_L sig n i  ⊨ R_move_to_blank_L_new sig n i.
#sig #n #i 
@(Realize_to_Realize … (sem_move_to_blank_L sig n i))
#t1 #t2 * #H1 #H2 % [@H1] 
#ls #a #rs #Ht1 lapply (H2 ls a rs Ht1) -H2 *
  [* #Ha #Ht2 >Ht2 %{a} %{[ ]} %{ls} 
   %[%[%[@Ha| //]| normalize //] | @Ht1]
  |* #b * #ls1 * #ls2 * * * #Hblank #Ht2
   %{b} %{(a::ls1)} %{ls2} 
   %[2:@Ht2|%[%[//|//]|
   #j #lejn whd in match (to_blank_i ????); 
   whd in match (to_blank_i ???(a::ls));
   lapply (Hblank j lejn) whd in match (to_blank_i ????);
   whd in match (to_blank_i ???(a::ls)); #H >H %
  ]
qed.

(******************************************************************************)
   
definition shift_i_L ≝ λsig,n,i.
   ncombf_r (multi_sig …) (shift_i sig n i) (all_blank sig n) ·
   mti sig n i · 
   extend ? (all_blank sig n).
   
definition R_shift_i_L ≝ λsig,n,i,t1,t2.
  (* ∀b:multi_sig sig n.∀ls.
    (t1 = midtape ? ls b [ ] → 
     t2 = midtape (multi_sig sig n) 
      ((shift_i sig n i b (all_blank sig n))::ls) (all_blank sig n) [ ]) ∧ *)
    (∀a,ls,rs. 
      t1 = midtape ? ls a rs  → 
      ((∃rs1,b,rs2,a1,rss.
        rs = rs1@b::rs2 ∧ 
        nth i ? (vec … b) (blank ?) = (blank ?) ∧
        (∀x. mem ? x rs1 → nth i ? (vec … x) (blank ?) ≠ (blank ?)) ∧
        shift_l sig n i (a::rs1) (a1::rss) ∧
        t2 = midtape (multi_sig sig n) ((reverse ? (a1::rss))@ls) b rs2) ∨
      (∃b,rss. 
        (∀x. mem ? x rs → nth i ? (vec … x) (blank ?) ≠ (blank ?)) ∧
        shift_l sig n i (a::rs) (rss@[b]) ∧
        t2 = midtape (multi_sig sig n) 
          ((reverse ? (rss@[b]))@ls) (all_blank sig n) [ ]))).

definition R_shift_i_L_new ≝ λsig,n,i,t1,t2.
  (∀a,ls,rs. 
   t1 = midtape ? ls a rs  → 
   ∃rs1,b,rs2,rss.
      b = hd ? rs2 (all_blank sig n) ∧
      nth i ? (vec … b) (blank ?) = (blank ?) ∧
      rs = rs1@rs2 ∧ 
      (∀x. mem ? x rs1 → nth i ? (vec … x) (blank ?) ≠ (blank ?)) ∧
      shift_l sig n i (a::rs1) rss ∧
      t2 = midtape (multi_sig sig n) ((reverse ? rss)@ls) b (tail ? rs2)). 
          
theorem sem_shift_i_L: ∀sig,n,i. shift_i_L sig n i  ⊨ R_shift_i_L sig n i.
#sig #n #i 
@(sem_seq_app ?????? 
  (sem_ncombf_r (multi_sig sig n) (shift_i sig n i)(all_blank sig n))
   (sem_seq ????? (ssem_mti sig n i) 
    (sem_extend ? (all_blank sig n))))
#tin #tout * #t1 * * #Ht1a #Ht1b * #t2 * * #Ht2a #Ht2b * #Htout1 #Htout2
(* #b #ls %
  [#Htin lapply (Ht1a … Htin) -Ht1a -Ht1b #Ht1 
   lapply (Ht2a … Ht1) -Ht2a -Ht2b #Ht2 >Ht2 in Htout1; 
   >Ht1 whd in match (left ??); whd in match (right ??); #Htout @Htout // *)
#a #ls #rs cases rs
  [#Htin %2 %{(shift_i sig n i a (all_blank sig n))} %{[ ]} 
   %[%[#x @False_ind | @daemon]
    |lapply (Ht1a … Htin) -Ht1a -Ht1b #Ht1 
     lapply (Ht2a … Ht1) -Ht2a -Ht2b #Ht2 >Ht2 in Htout1; 
     >Ht1 whd in match (left ??); whd in match (right ??); #Htout @Htout // 
    ]
  |#a1 #rs1 #Htin 
   lapply (Ht1b … Htin) -Ht1a -Ht1b #Ht1 
   lapply (Ht2b … Ht1) -Ht2a -Ht2b *
    [(* a1 is blank *) * #H1 #H2 %1
     %{[ ]} %{a1} %{rs1} %{(shift_i sig n i a a1)} %{[ ]}
     %[%[%[%[// |//] |#x @False_ind] | @daemon]
      |>Htout2 [>H2 >reverse_single @Ht1 |>H2 >Ht1 normalize % #H destruct (H)]
      ]
    |*
    [* #rs10 * #b * #rs2 * #rss * * * * #H1 #H2 #H3 #H4
     #Ht2 %1 
     %{(a1::rs10)} %{b} %{rs2} %{(shift_i sig n i a a1)} %{rss}
     %[%[%[%[>H1 //|//] |@H3] |@daemon ]
      |>reverse_cons >associative_append 
       >H2 in Htout2; #Htout >Htout [@Ht2| >Ht2 normalize % #H destruct (H)]  
      ]
    |* #b * #rss * * #H1 #H2 
     #Ht2 %2
     %{(shift_i sig n i b (all_blank sig n))} %{(shift_i sig n i a a1::rss)}
     %[%[@H1 |@daemon ]
      |>Ht2 in Htout1; #Htout >Htout //
       whd in match (left ??); whd in match (right ??);
       >reverse_append >reverse_single >associative_append  >reverse_cons
       >associative_append // 
       ]
     ]
   ]
 ]
qed.
 
theorem sem_shift_i_L_new: ∀sig,n,i. 
  shift_i_L sig n i  ⊨ R_shift_i_L_new sig n i.
#sig #n #i 
@(Realize_to_Realize … (sem_shift_i_L sig n i))
#t1 #t2 #H #a #ls #rs #Ht1 lapply (H a ls rs Ht1) *
  [* #rs1 * #b * #rs2 * #a1 * #rss * * * * #H1 #H2 #H3 #H4 #Ht2
   %{rs1} %{b} %{(b::rs2)} %{(a1::rss)} 
   %[%[%[%[%[//|@H2]|@H1]|@H3]|@H4] | whd in match (tail ??); @Ht2]
  |* #b * #rss * * #H1 #H2 #Ht2
   %{rs} %{(all_blank sig n)} %{[]} %{(rss@[b])} 
   %[%[%[%[%[//|@blank_all_blank]|//]|@H1]|@H2] | whd in match (tail ??); @Ht2]
  ]
qed.
   

(******************************************************************************)
definition no_head_in ≝ λsig,n,l. 
  ∀x. mem ? x (trace sig n n l) → x ≠ head ?.
  
lemma no_head_true: ∀sig,n,a. 
  nth n ? (vec … n a) (blank sig) ≠ head ? → no_head … a = true.
#sig #n #a normalize cases (nth n ? (vec … n a) (blank sig))
normalize // * normalize // * #H @False_ind @H //
qed.

lemma no_head_false: ∀sig,n,a. 
  nth n ? (vec … n a) (blank sig) = head ? → no_head … a = false.
#sig #n #a #H normalize >H //  
qed.

definition mtiL ≝ λsig,n,i.
   move_to_blank_L sig n i · 
   shift_i_L sig n i ·
   move_until ? L (no_head sig n). 
   
definition Rmtil ≝ λsig,n,i,t1,t2.
  ∀ls,a,rs. 
   t1 = midtape (multi_sig sig n) ls a rs → 
   nth n ? (vec … a) (blank ?) = head ? →   
   no_head_in … ls →   
   no_head_in … rs  → 
   (∃ls1,a1,rs1.
     t2 = midtape (multi_sig …) ls1 a1 rs1 ∧
     (∀j. j ≤ n → j ≠ i → to_blank_i ? n j (a1::ls1) = to_blank_i ? n j (a::ls)) ∧
     (∀j. j ≤ n → j ≠ i → to_blank_i ? n j rs1 = to_blank_i ? n j rs) ∧
     (to_blank_i ? n i ls1 = to_blank_i ? n i (a::ls)) ∧
     (to_blank_i ? n i (a1::rs1)) = to_blank_i ? n i rs).

lemma reverse_map: ∀A,B,f,l.
  reverse B (map … f l) = map … f (reverse A l).
#A #B #f #l elim l //
#a #l #Hind >reverse_cons >reverse_cons <map_append >Hind //
qed.
  
theorem sem_Rmtil: ∀sig,n,i. i < n → mtiL sig n i  ⊨ Rmtil sig n i.
#sig #n #i #lt_in
@(sem_seq_app ?????? 
  (sem_move_to_blank_L_new … )
   (sem_seq ????? (sem_shift_i_L_new …)
    (ssem_move_until_L ? (no_head sig n))))
#tin #tout * #t1 * * #_ #Ht1 * #t2 * #Ht2 * #_ #Htout
(* we start looking into Rmitl *)
#ls #a #rs #Htin (* tin is a midtape *)
#Hhead #Hnohead_ls #Hnohead_rs  
lapply (Ht1 … Htin) -Ht1 -Htin
* #b * #ls1 * #ls2 * * * #Hno_blankb #Hhead #Hls1 #Ht1
lapply (Ht2 … Ht1) -Ht2 -Ht1 
* #rs1 * #b0 * #rs2 * #rss * * * * * #Hb0 #Hb0blank #Hrs1 #Hrs1b #Hrss #Ht2
(* we need to recover the position of the head of the emulated machine
   that is the head of ls1. This is somewhere inside rs1 *) 
cut (∃rs11. rs1 = (reverse ? ls1)@rs11)
     [cut (ls1 = [ ] ∨ ∃aa,tlls1. ls1 = aa::tlls1)
       [cases ls1 [%1 // | #aa #tlls1 %2 %{aa} %{tlls1} //]] *
       [#H1ls1 %{rs1} >H1ls1 //
       |* #aa * #tlls1 #H1ls1 >H1ls1 in Hrs1; 
        cut (aa = a) [>H1ls1 in Hls1; #H @(to_blank_hd … H)] #eqaa >eqaa  
        #Hrs1_aux cases (compare_append … (sym_eq … Hrs1_aux)) #l *
         [* #H1 #H2 %{l} @H1
         |(* this is absurd : if l is empty, the case is as before.
           if l is not empty then it must start with a blank, since it is the
           frist character in rs2. But in this case we would have a blank 
           inside ls1=attls1 that is absurd *)
          @daemon
         ]]]   
   * #rs11 #H1
lapply (Htout … Ht2) -Htout -Ht2 *
  [(* the current character on trace i hold the head-mark.
      The case is absurd, since b0 is the head of rs2, that is a sublist of rs, 
      and the head-mark is not in rs *)
   @daemon
   (* something is missing 
   * #H @False_ind @(absurd ? H) @eqnot_to_noteq whd in ⊢ (???%);
   cut (rs2 = [ ] ∨ ∃c,rs21. rs2 = c::rs21)
    [cases rs2 [ %1 // | #c #rs22 %2 %{c} %{rs22} //]] 
   * (* by cases on rs2 *)
    [#Hrs2 >Hb0 >Hrs2 normalize >all_blank_n //
    |* #c * #rs22 #Hrs2 destruct (Hrs2) @no_head_true @Hnohead_rs
     > *)
  |* 
  [(* we reach the head position *)
   (* cut (trace sig n j (a1::ls20)=trace sig n j (ls1@b::ls2)) *)
   * #ls10 * #a1 * #ls20 * * * #Hls20 #Ha1 #Hnh #Htout
   cut (∀j.j ≠ i →
      trace sig n j (reverse (multi_sig sig n) rs1@b::ls2) = 
      trace sig n j (ls10@a1::ls20))
    [#j #ineqj >append_cons <reverse_cons >trace_def <map_append <reverse_map
     lapply (trace_shift_neq …lt_in ? (sym_not_eq … ineqj) … Hrss) [//] #Htr
     <(trace_def …  (b::rs1)) <Htr >reverse_map >map_append @eq_f @Hls20 ] 
   #Htracej
   cut (trace sig n i (reverse (multi_sig sig n) (rs1@[b0])@ls2) = 
        trace sig n i (ls10@a1::ls20))
    [>trace_def <map_append <reverse_map <map_append <(trace_def … [b0]) 
     cut (trace sig n i [b0] = [blank ?]) [@daemon] #Hcut >Hcut
     lapply (trace_shift … lt_in … Hrss) [//] whd in match (tail ??); #Htr <Htr
     >reverse_map >map_append <trace_def <Hls20 % 
    ] 
   #Htracei
   cut (∀j. j ≠ i →
      (trace sig n j (reverse (multi_sig sig n) rs11) = trace sig n j ls10) ∧ 
      (trace sig n j (ls1@b::ls2) = trace sig n j (a1::ls20)))
   [@daemon (* si fa 
     #j #ineqj @(first_P_to_eq ? (λx. x ≠ head ?))
      [lapply (Htracej … ineqj) >trace_def in ⊢ (%→?); <map_append 
       >trace_def in ⊢ (%→?); <map_append #H @H  
      | *) ] #H2
  cut ((trace sig n i (b0::reverse ? rs11) = trace sig n i (ls10@[a1])) ∧ 
      (trace sig n i (ls1@ls2) = trace sig n i ls20))
    [>H1 in Htracei; >reverse_append >reverse_single >reverse_append 
     >reverse_reverse >associative_append >associative_append
     @daemon
    ] #H3
   %{ls20} %{a1} %{(reverse ? (b0::ls10)@tail (multi_sig sig n) rs2)}
   %[%[%[%[@Htout
    |#j #lejn #jneqi <(Hls1 … lejn) 
     >to_blank_i_def >to_blank_i_def @eq_f @sym_eq @(proj2 … (H2 j jneqi))]
    |#j #lejn #jneqi >reverse_cons >associative_append >Hb0
     <to_blank_hd_cons >to_blank_i_def >to_blank_i_def @eq_f
     @(injective_append_l … (trace sig n j (reverse ? ls1))) (* >trace_def >trace_def *)
     >map_append >map_append >Hrs1 >H1 >associative_append 
     <map_append <map_append in ⊢ (???%); @eq_f 
     <map_append <map_append @eq_f2 // @sym_eq 
     <(reverse_reverse … rs11) <reverse_map <reverse_map in ⊢ (???%);
     @eq_f @(proj1 … (H2 j jneqi))]
    |<(Hls1 i) [2:@lt_to_le //] (* manca un invariante: dopo un blank
     posso avere solo blank *) @daemon ]
    |>reverse_cons >associative_append  
     cut (to_blank_i sig n i rs = to_blank_i sig n i (rs11@[b0])) [@daemon] 
     #Hcut >Hcut >(to_blank_i_chop  … b0 (a1::reverse …ls10)) [2: @Hb0blank]
     >to_blank_i_def >to_blank_i_def @eq_f 
     >trace_def >trace_def @injective_reverse >reverse_map >reverse_cons
     >reverse_reverse >reverse_map >reverse_append >reverse_single @sym_eq
     @(proj1 … H3)
    ]
  |(*we do not find the head: this is absurd *)
   * #b1 * #lss * * #H2 @False_ind 
   cut (∀x0. mem ? x0 (trace sig n n (b0::reverse ? rss@ls2)) → x0 ≠ head ?)
     [@daemon] -H2 #H2
   lapply (trace_shift_neq sig n i n … lt_in … Hrss)
     [@lt_to_not_eq @lt_in | // ] 
   #H3 @(absurd 
        (nth n ? (vec … (hd ? (ls1@[b]) (all_blank sig n))) (blank ?) = head ?))
     [>Hhead //
     |@H2 >trace_def %2 <map_append @mem_append_l1 <reverse_map <trace_def 
      >H3 >H1 >trace_def >reverse_map >reverse_cons >reverse_append 
      >reverse_reverse >associative_append <map_append @mem_append_l2
      cases ls1 [%1 % |#x #ll %1 %]
     ]
   
  
   
   
(*
  
   cut (∀j.i ≠ j →
      trace sig n j (reverse (multi_sig sig n) rss@ls2) = 
      trace sig n j (ls10@a1::ls20))
    [#j #ineqj >trace_def <map_append in ⊢ (??%?); 
     <reverse_map lapply (trace_shift_neq …lt_in ? ineqj … Hrss) [//] #Htr
     <trace_def <trace_def >Htr >reverse_cons *)
    
   %{ls20} %{a1} %{(reverse ? (b0::ls10)@tail (multi_sig sig n) rs2)}
   %[%[%[%[%[@Htout
    |#j #lejn #jneqi <(Hls1 … lejn) -Hls1 
     >to_blank_i_def >to_blank_i_def @eq_f 
     @(injective_append_l … (trace sig n j (reverse ? rs))) (* >trace_def >trace_def *)
     >map_append >map_append
    
     ]
    |@daemon]
    |@daemon]
    |@daemon]
    |
   
   
  [(* the current character on trace i is blank *)
   * #Hblank #Ht1 <Ht1 in Htin; #Ht1a >Ht1a in Ht2;
   #Ht2 lapply (Ht2 … (refl …)) *
    [(* we reach the margin of the i-th trace *)
     * #rs1 * #b * #rs2 * #a1 * #rss * * * * #H1 #H2 #H3 #H4 #Ht2
     lapply (Htout … Ht2) -Htout *
      [(* the head is on b: this is absurd *)
       * #Hhb @False_ind >Hnohead_rs in Hhb; 
        [#H destruct (H) | >H1 @mem_append_l2 %1 //]
      |*
      [(* we reach the head position *)
       * #ls1 * #b0 * #ls2 * * * #H5 #H6 #H7 #Htout
       %{ls2} %{b0} %{(reverse ? (b::ls1)@rs2)}
       cut (ls2 = ls)
         [@daemon (* da finire 
          lapply H5 lapply H4 -H5 -H4 cases rss
           [* normalize in ⊢ (%→?); #H destruct (H)
           |#rssa #rsstl #H >reverse_cons >associative_append
            normalize in ⊢ (??(???%)%→?); #H8 @sym_eq
            @(first_P_to_eq (multi_sig sig n)
              (λa.nth n (sig_ext sig) (vec … a) (blank ?) = head ?) ?????? H8)
          *)
         ] #Hls
       %[%[%[%[%[@Htout|>Hls //]
              | #j #lejn #neji >to_blank_i_def >to_blank_i_def
               @eq_f >H1 >trace_def >trace_def >reverse_cons
               >associative_append <map_append <map_append in ⊢ (???%); @eq_f2 //
               @daemon] 
             |//]
           |* #H @False_ind @H @daemon
           ] 
         |>H1 @daemon
         ]
     |(* we do not find the head: absurd *)
      cut (nth n (sig_ext sig) (vec … a1) (blank sig)=head sig)
        [lapply (trace_shift_neq ??? n … lt_in … H4)
          [@lt_to_not_eq // |//] 
         whd in match (trace ????); whd in match (trace ???(a::rs1));
         #H <Hhead @(cons_injective_l … H)]
       #Hcut * #b0 * #lss * * #H @False_ind
       @(absurd (true=false)) [2://] <(H a1) 
        [whd in match (no_head ???); >Hcut //
        |%2 @mem_append_l1 >reverse_cons @mem_append_l2 %1 //
        ]
     ]

theorem sem_Rmtil: ∀sig,n,i. i < n → mtiL sig n i  ⊨ Rmtil sig n i.
#sig #n #i #lt_in
@(sem_seq_app ?????? 
  (sem_move_to_blank_L … )
   (sem_seq ????? (sem_shift_i_L …)
    (ssem_move_until_L ? (no_head sig n))))
#tin #tout * #t1 * * #_ #Ht1 * #t2 * #Ht2 * #_ #Htout
(* we start looking into Rmitl *)
#ls #a #rs #Htin (* tin is a midtape *)
#Hhead #Hnohead_ls #Hnohead_rs  
cases (Ht1 … Htin) -Ht1
  [(* the current character on trace i is blank *)
   * #Hblank #Ht1 <Ht1 in Htin; #Ht1a >Ht1a in Ht2;
   #Ht2 lapply (Ht2 … (refl …)) *
    [(* we reach the margin of the i-th trace *)
     * #rs1 * #b * #rs2 * #a1 * #rss * * * * #H1 #H2 #H3 #H4 #Ht2
     lapply (Htout … Ht2) -Htout *
      [(* the head is on b: this is absurd *)
       * #Hhb @False_ind >Hnohead_rs in Hhb; 
        [#H destruct (H) | >H1 @mem_append_l2 %1 //]
      |*
      [(* we reach the head position *)
       * #ls1 * #b0 * #ls2 * * * #H5 #H6 #H7 #Htout
       %{ls2} %{b0} %{(reverse ? (b::ls1)@rs2)}
       cut (ls2 = ls)
         [@daemon (* da finire 
          lapply H5 lapply H4 -H5 -H4 cases rss
           [* normalize in ⊢ (%→?); #H destruct (H)
           |#rssa #rsstl #H >reverse_cons >associative_append
            normalize in ⊢ (??(???%)%→?); #H8 @sym_eq
            @(first_P_to_eq (multi_sig sig n)
              (λa.nth n (sig_ext sig) (vec … a) (blank ?) = head ?) ?????? H8)
          *)
         ] #Hls
       %[%[%[%[%[@Htout|>Hls //]
              | #j #lejn #neji >to_blank_i_def >to_blank_i_def
               @eq_f >H1 >trace_def >trace_def >reverse_cons
               >associative_append <map_append <map_append in ⊢ (???%); @eq_f2 //
               @daemon] 
             |//]
           |* #H @False_ind @H @daemon
           ] 
         |>H1 @daemon
         ]
     |(* we do not find the head: absurd *)
      cut (nth n (sig_ext sig) (vec … a1) (blank sig)=head sig)
        [lapply (trace_shift_neq ??? n … lt_in … H4)
          [@lt_to_not_eq // |//] 
         whd in match (trace ????); whd in match (trace ???(a::rs1));
         #H <Hhead @(cons_injective_l … H)]
       #Hcut * #b0 * #lss * * #H @False_ind
       @(absurd (true=false)) [2://] <(H a1) 
        [whd in match (no_head ???); >Hcut //
        |%2 @mem_append_l1 >reverse_cons @mem_append_l2 %1 //
        ]
     ]


theorem sem_Rmtil: ∀sig,n,i. mtiL sig n i  ⊨ Rmtil sig n i.
#sig #n #i 
@(sem_seq_app ?????? 
  (ssem_move_until_L ? (no_blank sig n i))
   (sem_seq ????? (sem_extend ? (all_blank sig n))
    (sem_seq ????? (sem_ncombf_r (multi_sig sig n) (shift_i sig n i)(all_blank sig n))
     (sem_seq ????? (ssem_mti sig n i) 
      (sem_seq ????? (sem_extend ? (all_blank sig n)) 
       (ssem_move_until_L ? (no_head sig n)))))))
#tin #tout * #t1 * * #_ #Ht1 * #t2 * * #Ht2a #Ht2b * #t3 * * #Ht3a #Ht3b 
* #t4 * * #Ht4a #Ht4b * #t5 * * #Ht5a #Ht5b * #t6 #Htout
(* we start looking into Rmitl *)
#ls #a #rs #Htin (* tin is a midtape *)
#Hhead #Hnohead_ls #Hnohead_rs  
cases (Ht1 … Htin) -Ht1 
  [(* the current character on trace i is blank *)
   -Ht2a * #Hblank #Ht1 <Ht1 in Htin; #Ht1a >Ht1a in Ht2b;
   #Ht2b lapply (Ht2b ?) [% normalize #H destruct] -Ht2b -Ht1 -Ht1a 
   lapply Hnohead_rs -Hnohead_rs
   (* by cases on rs *) cases rs
    [#_ (* rs is empty *) #Ht2 -Ht3b lapply (Ht3a … Ht2)
     #Ht3 -Ht4b lapply (Ht4a … Ht3) -Ht4a #Ht4 -Ht5b
     >Ht4 in Ht5a; >Ht3 #Ht5a lapply (Ht5a (refl … )) -Ht5a #Ht5
     cases (Htout … Ht5) -Htout
      [(* the current symbol on trace n is the head: this is absurd *)
       * whd in ⊢ (??%?→?); >all_blank_n whd in ⊢ (??%?→?); #H destruct (H)
      |*
      [(* we return to the head *)
       * #ls1 * #b * #ls2 * * * whd in ⊢ (??%?→?);
       #H1 #H2 #H3 
       (* ls1 must be empty *)
       cut (ls1=[]) 
        [lapply H3 lapply H1 -H3 -H1 cases ls1 // #c #ls3
         whd in ⊢ (???%→?); #H1 destruct (H1) 
         >blank_all_blank [|@daemon] #H @False_ind 
         lapply (H … (change_vec (sig_ext sig) n a (blank sig) i) ?) 
          [%2 %1 // | whd in match (no_head ???); >nth_change_vec_neq [|@daemon]
           >Hhead whd in ⊢ (??%?→?); #H1 destruct (H1)]] 
       #Hls1_nil >Hls1_nil in H1; whd in ⊢ (???%→?); #H destruct (H)
       >reverse_single >blank_all_blank [|@daemon]
       whd in match (right ??) ; >append_nil #Htout
       %{ls2} %{(change_vec (sig_ext sig) n a (blank sig) i)} %{[all_blank sig n]}
       %[%[%[%[%[//|//]|@daemon]|//] |(*absurd*)@daemon] 
        |normalize >nth_change_vec // @daemon]
      |(* we do not find the head: this is absurd *)
       * #b * #lss * * whd in match (left ??); #HF @False_ind
       lapply (HF … (shift_i sig n i a (all_blank sig n)) ?) [%2 %1 //] 
       whd in match (no_head ???); >nth_change_vec_neq [|@daemon]
       >Hhead whd in ⊢ (??%?→?); #H destruct (H)
      ]
      ]
    |(* rs = c::rs1 *)
     #c #rs1 #Hnohead_rs #Ht2 -Ht3a lapply (Ht3b … Ht2) -Ht3b
     #Ht3 -Ht4a lapply (Ht4b … Ht3) -Ht4b *
      [(* the first character is blank *) *
       #Hblank #Ht4 -Ht5a >Ht4 in Ht5b; >Ht3 
       normalize in ⊢ ((%→?)→?); #Ht5 lapply (Ht5 ?) [% #H destruct (H)] 
       -Ht2 -Ht3 -Ht4 -Ht5 #Ht5 cases (Htout … Ht5) -Htout
        [(* the current symbol on trace n is the head: this is absurd *)
         * >Hnohead_rs [#H destruct (H) |%1 //]
        |*
        [(* we return to the head *)
         * #ls1 * #b * #ls2 * * * whd in ⊢ (??%?→?);
         #H1 #H2 #H3 
         (* ls1 must be empty *)
         cut (ls1=[]) 
          [lapply H3 lapply H1 -H3 -H1 cases ls1 // #x #ls3
           whd in ⊢ (???%→?); #H1 destruct (H1) #H @False_ind
           lapply (H (change_vec (sig_ext sig) n a (nth i (sig_ext sig) (vec … c) (blank sig)) i) ?)
            [%2 %1 // | whd in match (no_head ???); >nth_change_vec_neq [|@daemon]
             >Hhead whd in ⊢ (??%?→?); #H1 destruct (H1)]] 
         #Hls1_nil >Hls1_nil in H1; whd in ⊢ (???%→?); #H destruct (H)
         >reverse_single #Htout
         %{ls2} %{(change_vec (sig_ext sig) n a (nth i (sig_ext sig) (vec … c) (blank sig)) i)} 
         %{(c::rs1)}
         %[%[%[%[%[@Htout|//]|//]|//] |(*absurd*)@daemon] 
          |>to_blank_cons_b
             [>(to_blank_cons_b … Hblank) //| >nth_change_vec [@Hblank |@daemon]] 
          ]
        |(* we do not find the head: this is absurd *)
         * #b * #lss * * #HF @False_ind
         lapply (HF … (shift_i sig n i a c) ?) [%2 %1 //] 
         whd in match (no_head ???); >nth_change_vec_neq [|@daemon]
         >Hhead whd in ⊢ (??%?→?); #H destruct (H)
        ]
      ]
    |
    
  (* end of the first case !! *)
       
        
    
   #Ht2
    
cut (∃rs11,rs12. b::rs1 = rs11@a::rs12 ∧ no_head_in ?? rs11)
     [cut (ls1 = [ ] ∨ ∃aa,tlls1. ls1 = aa::tlls1)
       [cases ls1 [%1 // | #aa #tlls1 %2 %{aa} %{tlls1} //]] *
       [#H1ls1 %{[ ]} %{rs1} %
         [ @eq_f2 // >H1ls1 in Hls1; whd in match ([]@b::ls2); 
           #Hls1 @(to_blank_hd … Hls1)
         |normalize #x @False_ind
         ]
       |* #aa * #tlls1 #H1ls1 >H1ls1 in Hrs1; 
        cut (aa = a) [>H1ls1 in Hls1; #H @(to_blank_hd … H)] #eqaa >eqaa  
        #Hrs1_aux cases (compare_append … (sym_eq … Hrs1_aux)) #l *
         [* #H1 #H2 %{(b::(reverse ? tlls1))} %{l} %
           [@eq_f >H1 >reverse_cons >associative_append //
           |@daemon (* is a sublit of the tail of ls1, and hence of ls *)
           ]
         |(* this is absurd : if l is empty, the case is as before.
           if l is not empty then it must start with a blank, since it is the
           frist character in rs2. But in this case we would have a blank 
           inside ls1=attls1 that is absurd *)
          @daemon
         ]]] 



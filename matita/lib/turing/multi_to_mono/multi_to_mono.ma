include "turing/auxiliary_machines1.ma".
include "turing/multi_to_mono/shift_trace_machines.ma".

(******************************************************************************)
(* mtiL: complete move L for tape i. We reaching the left border of trace i,  *)
(* add a blank if there is no more tape, then move the i-trace and finally    *)
(* come back to the head position.                                            *)
(******************************************************************************)

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
   ]
 ]
qed.

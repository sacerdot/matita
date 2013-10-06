include "turing/basic_machines.ma".
include "turing/if_machine.ma".
include "basics/vector_finset.ma".
include "turing/auxiliary_machines1.ma".

(* a multi_sig characheter is composed by n+1 sub-characters: n for each tape 
of a multitape machine, and an additional one to mark the position of the head. 
We extend the tape alphabet with two new symbols true and false. 
false is used to pad shorter tapes, and true to mark the head of the tape *)

definition sig_ext ≝ λsig. FinSum FinBool sig.
definition blank : ∀sig.sig_ext sig ≝ λsig. inl … false.
definition head : ∀sig.sig_ext sig ≝ λsig. inl … true.

definition multi_sig ≝ λsig:FinSet.λn.FinVector (sig_ext sig) n.

let rec all_blank sig n on n : multi_sig sig n ≝ 
  match n with
  [ O ⇒ Vector_of_list ? []
  | S m ⇒ vec_cons ? (blank ?) m (all_blank sig m)
  ].

lemma blank_all_blank: ∀sig,n,i. i ≤ n →
  nth i ? (vec … (all_blank sig n)) (blank sig) = blank ?.
#sig #n elim n normalize
  [#i #lei0 @(le_n_O_elim … lei0) normalize // 
  |#m #Hind #i cases i // #j #lej @Hind @le_S_S_to_le //
  ]
qed.

lemma all_blank_n: ∀sig,n.
  nth n ? (vec … (all_blank sig n)) (blank sig) = blank ?.
#sig #n @blank_all_blank //
qed.


(* a machine that moves the i trace r: we reach the left margin of the i-trace 
and make a (shifted) copy of the old tape up to the end of the right margin of 
the i-trace. Then come back to the origin. *)

(* definition move_r_i *)

(* move_tape_i_step:
   we cycle on normal chars *)
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
  |v1| = |v2| ∧ ∀j. S j < |v1| → 
    nth j ? v2 (all_blank sig n) = 
      change_vec ? n (nth j ? v1 (all_blank sig n)) 
        (nth i ? (vec … (nth (S j) ? v1 (all_blank sig n))) (blank ?)) i.

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

definition mtiL ≝ λsig,n,i.
   move_until ? L (no_blank sig n i) · 
   extend ? (all_blank sig n) ·
   ncombf_r (multi_sig …) (shift_i sig n i) (all_blank sig n) ·
   mti sig n i · 
   extend ? (all_blank sig n) ·
   move_until ? L (no_head sig n). 
   
let rec to_blank sig n i l on l ≝
  match l with
  [ nil ⇒  [ ]
  | cons a tl ⇒ 
      let ai ≝ nth i ? (vec … n a) (blank sig) in
      if ai == blank ? then [ ] else ai::(to_blank sig n i tl)]. 
      
lemma to_blank_cons_b : ∀sig,n,i,a,l.
  nth i ? (vec … n a) (blank sig) = blank ? →
  to_blank sig n i (a::l) = [ ].
#sig #n #i #a #l #H whd in match (to_blank ????);
>(\b H) //
qed.      

lemma to_blank_cons_nb: ∀sig,n,i,a,l.
  nth i ? (vec … n a) (blank sig) ≠ blank ? →
  to_blank sig n i (a::l) = 
    nth i ? (vec … n a) (blank sig)::(to_blank sig n i l).
#sig #n #i #a #l #H whd in match (to_blank ????);
>(\bf H) //
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
    (∀j.j ≤n → to_blank ?? j (ls1@b::ls2) = to_blank ?? j ls) ∧
    t2 = midtape ? ls2 b ((reverse ? (a::ls1))@rs)).

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
      ((∃rs1,b,rs2,rss.
        rs = rs1@b::rs2 ∧ 
        nth i ? (vec … b) (blank ?) = (blank ?) ∧
        (∀x. mem ? x rs1 → nth i ? (vec … x) (blank ?) ≠ (blank ?)) ∧
        shift_l sig n i (a::rs1) rss ∧
        t2 = midtape (multi_sig sig n) ((reverse ? rss)@ls) b rs2) ∨
      (∃b,rss. 
        (∀x. mem ? x rs → nth i ? (vec … x) (blank ?) ≠ (blank ?)) ∧
        shift_l sig n i (a::rs) (rss@[b]) ∧
        t2 = midtape (multi_sig sig n) 
          ((reverse ? (rss@[b]))@ls) (all_blank sig n) [ ]))).

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
     %{[ ]} %{a1} %{rs1} %{[shift_i sig n i a a1]}
     %[%[%[%[// |//] |#x @False_ind] | @daemon]
      |>Htout2 [>H2 >reverse_single @Ht1 |>H2 >Ht1 normalize % #H destruct (H)]
      ]
    |*
    [* #rs10 * #b * #rs2 * #rss * * * * #H1 #H2 #H3 #H4
     #Ht2 %1 
     %{(a1::rs10)} %{b} %{rs2} %{(shift_i sig n i a a1::rss)}
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
 
    
definition Rmtil ≝ λsig,n,i,t1,t2.
  ∀ls,a,rs. 
   t1 = midtape ? ls a rs → 
   nth n ? (vec … a) (blank ?) = head ? →   
   (∀x.mem ? x ls → no_head sig n x = true) →   
   (∀x.mem ? x rs → no_head sig n x = true) → 
   (∃ls1,a1,rs1.
     t2 = midtape (multi_sig …) ls1 a1 rs1 ∧
     (∀j. j ≤ n → j ≠ i → to_blank ? n j ls1 = to_blank ? n j ls) ∧
     (∀j. j ≤ n → j ≠ i → to_blank ? n j rs1 = to_blank ? n j rs) ∧
     (nth i ? (vec … a) (blank ?) = blank ? → ls1 = ls) ∧
     (nth i ? (vec … a) (blank ?) ≠ blank ? → to_blank ? n i ls1 = nth i ? (vec … a) (blank ?)::to_blank ? n i ls) ∧
     (to_blank ? n i (a1::rs1)) = to_blank ? n i rs).

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
    




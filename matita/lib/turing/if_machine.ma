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

include "turing/mono.ma".

definition single_finalTM ≝ 
  λsig.λM:TM sig.seq ? M (nop ?).

lemma sem_single_final :
  ∀sig,M,R.Realize ? M R → Realize ? (single_finalTM sig M) R.
#sig #M #R #HR #intape 
cases (sem_seq ????? HR (sem_nop …) intape)
#k * #outc * #Hloop * #ta * #Hta whd in ⊢ (%→?); #Houtc
@(ex_intro ?? k) @(ex_intro ?? outc) %  [ @Hloop | >Houtc // ]
qed.

definition if_trans ≝ λsig. λM1,M2,M3 : TM sig. λq:states sig M1.
λp. let 〈s,a〉 ≝ p in
  match s with 
  [ inl s1 ⇒ 
      if halt sig M1 s1 then
        if s1==q then 〈inr … (inl … (start sig M2)), None ?〉
        else 〈inr … (inr … (start sig M3)), None ?〉
      else let 〈news1,m〉 ≝ trans sig M1 〈s1,a〉 in
       〈inl … news1,m〉
  | inr s' ⇒ 
      match s' with
      [ inl s2 ⇒ let 〈news2,m〉 ≝ trans sig M2 〈s2,a〉 in
         〈inr … (inl … news2),m〉
      | inr s3 ⇒ let 〈news3,m〉 ≝ trans sig M3 〈s3,a〉 in
         〈inr … (inr … news3),m〉
      ]
  ]. 
 
definition ifTM ≝ λsig. λcondM,thenM,elseM : TM sig.
  λqacc: states sig condM.
  mk_TM sig 
    (FinSum (states sig condM) (FinSum (states sig thenM) (states sig elseM)))
    (if_trans sig condM thenM elseM qacc)
    (inl … (start sig condM))
    (λs.match s with
      [ inl _ ⇒ false 
      | inr s' ⇒ match s' with 
        [ inl s2 ⇒ halt sig thenM s2
        | inr s3 ⇒ halt sig elseM s3 ]]).
        
axiom daemon : ∀X:Prop.X.
axiom tdaemon : ∀X:Type[0].X.

axiom sem_if: ∀sig,M1,M2,M3,Rtrue,Rfalse,R2,R3,acc.
  accRealize sig M1 acc Rtrue Rfalse → Realize sig M2 R2 → Realize sig M3 R3 → 
    Realize sig (ifTM sig M1 M2 M3 acc) (λt1,t2. (Rtrue ∘ R2) t1 t2 ∨ (Rfalse ∘ R3) t1 t2).
    
lemma sem_if_app: ∀sig,M1,M2,M3,Rtrue,Rfalse,R2,R3,R4,acc.
  accRealize sig M1 acc Rtrue Rfalse → Realize sig M2 R2 → Realize sig M3 R3 → 
    (∀t1,t2,t3. (Rtrue t1 t3 ∧ R2 t3 t2) ∨ (Rfalse t1 t3 ∧ R3 t3 t2) → R4 t1 t2) →  
    Realize sig 
     (ifTM sig M1 M2 M3 acc) R4.
#sig #M1 #M2 #M3 #Rtrue #Rfalse #R2 #R3 #R4 #acc
#HRacc #HRtrue #HRfalse #Hsub
#t cases (sem_if … HRacc HRtrue HRfalse t)
#k * #outc * #Hloop #Houtc @(ex_intro … k) @(ex_intro … outc)
% [@Hloop] cases Houtc
  [* #t3 * #Hleft #Hright @(Hsub … t3) %1 /2/
  |* #t3 * #Hleft #Hright @(Hsub … t3) %2 /2/ ]
qed.

axiom acc_sem_if: ∀sig,M1,M2,M3,Rtrue,Rfalse,R2,R3,acc.
  accRealize sig M1 acc Rtrue Rfalse → Realize sig M2 R2 → Realize sig M3 R3 → 
    accRealize sig 
     (ifTM sig M1 (single_finalTM … M2) M3 acc) 
     (inr … (inl … (inr … start_nop)))
     (Rtrue ∘ R2) 
     (Rfalse ∘ R3).
     
lemma acc_sem_if_app: ∀sig,M1,M2,M3,Rtrue,Rfalse,R2,R3,R4,R5,acc.
  accRealize sig M1 acc Rtrue Rfalse → Realize sig M2 R2 → Realize sig M3 R3 → 
    (∀t1,t2,t3. Rtrue t1 t3 → R2 t3 t2 → R4 t1 t2) → 
    (∀t1,t2,t3. Rfalse t1 t3 → R3 t3 t2 → R5 t1 t2) → 
    accRealize sig 
     (ifTM sig M1 (single_finalTM … M2) M3 acc) 
     (inr … (inl … (inr … start_nop)))
     R4 R5.    
#sig #M1 #M2 #M3 #Rtrue #Rfalse #R2 #R3 #R4 #R5 #acc
#HRacc #HRtrue #HRfalse #Hsub1 #Hsub2 
#t cases (acc_sem_if … HRacc HRtrue HRfalse t)
#k * #outc * * #Hloop #Houtc1 #Houtc2 @(ex_intro … k) @(ex_intro … outc)
% [% [@Hloop
     |#H cases (Houtc1 H) #t3 * #Hleft #Hright @Hsub1 // ]
  |#H cases (Houtc2 H) #t3 * #Hleft #Hright @Hsub2 // ]
qed.

(*    
#sig #M1 #M2 #M3 #Rtrue #Rfalse #R2 #R3 #acc #HaccR #HR2 #HR3 #t 
cases (HaccR t) #k1 * #outc1 * * #Hloop1 #HMtrue #HMfalse 
cases (true_or_false (cstate ?? outc1 == acc)) #Hacc
  [cases (HR2 (ctape sig ? outc1)) #k2 * #outc2 * #Hloop2 #HM2
   @(ex_intro … (k1+k2)) @(ex_intro … (lift_confR … (lift_confL … outc2)))
   %
   [@(loop_merge ??????????? 
    (loop_lift ??? 
      (lift_confL sig (states ? M1) (FinSum (states ? M2) (states ? M3)))
      (step sig M1) (step sig (ifTM sig M1 M2 M3 acc)) 
      (λc.halt sig M1 (cstate … c)) 
      (λc.halt_liftL ?? (halt sig M1) (cstate … c)) 
      … Hloop1))
     [* *
       [ #sl #tl whd in ⊢ (??%? → ?); #Hl %
       | #sr #tr whd in ⊢ (??%? → ?); #Hr destruct (Hr) ]
     || #c0 #Hhalt @daemon  (* <step_lift_confL // *)
     | #x <p_halt_liftL %
     |6:cases outc1 #s1 #t1 %
     |7:@(loop_lift … (initc ?? (ctape … outc1)) … Hloop2) 
       [ * #s2 #t2 %
       | #c0 #Hhalt @daemon (* <step_lift_confR // *) ]
     |whd in ⊢ (??(???%)?);whd in ⊢ (??%?);
      generalize in match Hloop1; cases outc1 #sc1 #tc1 #Hloop10 
      >(trans_liftL_true sig M1 M2 ??) 
       [ whd in ⊢ (??%?); whd in ⊢ (???%);
         @daemon
(*         @config_eq whd in ⊢ (???%); // *)
       | @(loop_Some ?????? Hloop10)
       | @tdaemon 
       | skip ]
      ]
     |
     |4:cases outc1 #s1 #t1 %
     |5:
         
         @(loop_liftR … Hloop2) 
         |whd in ⊢ (??(???%)?);whd in ⊢ (??%?);
          generalize in match Hloop1; cases outc1 #sc1 #tc1 #Hloop10 
          >(trans_liftL_true sig M1 M2 ??) 
           [ whd in ⊢ (??%?); whd in ⊢ (???%);
             @config_eq //
           | @(loop_Some ?????? Hloop10) ]
           ]
| @(ex_intro … (ctape ? (seq sig M1 M2) (lift_confL … outc1)))
  % //
]
qed.
*)
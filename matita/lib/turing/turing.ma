include "turing/mono.ma".
include "basics/vectors.ma".

(* We do not distinuish an input tape *)

record mTM (sig:FinSet): Type[1] ≝ 
{ states : FinSet;
  tapes_no: nat; (* additional working tapes *)
  trans : states × (Vector (option sig) (S tapes_no)) → 
    states  × (Vector (option (sig × move))(S tapes_no));
  start: states;
  halt : states → bool
}.

record mconfig (sig,states:FinSet) (n:nat): Type[0] ≝
{ cstate : states;
  ctapes : Vector (tape sig) (S n)
}.

definition current_chars ≝ λsig.λn.λtapes.
  vec_map ?? (current sig) (S n) tapes.

definition step ≝ λsig.λM:mTM sig.λc:mconfig sig (states ? M) (tapes_no ? M).
  let 〈news,mvs〉 ≝ trans sig M 〈cstate ??? c,current_chars ?? (ctapes ??? c)〉 in
  mk_mconfig ??? 
    news 
    (pmap_vec ??? (tape_move sig) ? (ctapes ??? c) mvs).

definition empty_tapes ≝ λsig.λn.
mk_Vector ? n (make_list (tape sig) (niltape sig) n) ?.
elim n // normalize //
qed.

(************************** Realizability *************************************)
definition loopM ≝ λsig.λM:mTM sig.λi,cin.
  loop ? i (step sig M) (λc.halt sig M (cstate ??? c)) cin.

lemma loopM_unfold : ∀sig,M,i,cin.
  loopM sig M i cin = loop ? i (step sig M) (λc.halt sig M (cstate ??? c)) cin.
// qed.

definition initc ≝ λsig.λM:mTM sig.λtapes.
  mk_mconfig sig (states sig M) (tapes_no sig M) (start sig M) tapes.

definition Realize ≝ λsig.λM:mTM sig.λR:relation (Vector (tape sig) ?).
∀t.∃i.∃outc.
  loopM sig M i (initc sig M t) = Some ? outc ∧ R t (ctapes ??? outc).

definition WRealize ≝ λsig.λM:mTM sig.λR:relation (Vector (tape sig) ?).
∀t,i,outc.
  loopM sig M i (initc sig M t) = Some ? outc → R t (ctapes ??? outc).

definition Terminate ≝ λsig.λM:mTM sig.λt. ∃i,outc.
  loopM sig M i (initc sig M t) = Some ? outc.
  
(* notation "M \vDash R" non associative with precedence 45 for @{ 'models $M $R}. *)
interpretation "multi realizability" 'models M R = (Realize ? M R).

(* notation "M \VDash R" non associative with precedence 45 for @{ 'wmodels $M $R}. *)
interpretation "weak multi realizability" 'wmodels M R = (WRealize ? M R).

interpretation "multi termination" 'fintersects M t = (Terminate ? M t).

lemma WRealize_to_Realize : ∀sig.∀M: mTM sig.∀R.
  (∀t.M ↓ t) → M ⊫ R → M ⊨ R.
#sig #M #R #HT #HW #t cases (HT … t) #i * #outc #Hloop 
@(ex_intro … i) @(ex_intro … outc) % // @(HW … i) //
qed.

theorem Realize_to_WRealize : ∀sig.∀M:mTM sig.∀R.
  M ⊨ R → M ⊫ R.
#sig #M #R #H1 #inc #i #outc #Hloop 
cases (H1 inc) #k * #outc1 * #Hloop1 #HR >(loop_eq … Hloop Hloop1) //
qed.

definition accRealize ≝ λsig.λM:mTM sig.λacc:states sig M.λRtrue,Rfalse.
∀t.∃i.∃outc.
  loopM sig M i (initc sig M t) = Some ? outc ∧
    (cstate ??? outc = acc → Rtrue t (ctapes ??? outc)) ∧ 
    (cstate ??? outc ≠ acc → Rfalse t (ctapes ??? outc)).
    
(* notation "M ⊨ [q: R1,R2]" non associative with precedence 45 for @{ 'cmodels $M $q $R1 $R2}. *)
interpretation "conditional multi realizability" 'cmodels M q R1 R2 = (accRealize ? M q R1 R2).

(*************************** guarded realizablity *****************************)
definition GRealize ≝ λsig.λM:mTM sig.λPre:Vector (tape sig) ? →Prop.λR:relation (Vector (tape sig) ?).
∀t.Pre t → ∃i.∃outc.
  loopM sig M i (initc sig M t) = Some ? outc ∧ R t (ctapes ??? outc).
  
definition accGRealize ≝ λsig.λM:mTM sig.λacc:states sig M.
λPre: Vector (tape sig) ? → Prop.λRtrue,Rfalse.
∀t.Pre t → ∃i.∃outc.
  loopM sig M i (initc sig M t) = Some ? outc ∧
    (cstate ??? outc = acc → Rtrue t (ctapes ??? outc)) ∧ 
    (cstate ??? outc ≠ acc → Rfalse t (ctapes ??? outc)).
    
lemma WRealize_to_GRealize : ∀sig.∀M: mTM sig.∀Pre,R.
  (∀t.Pre t → M ↓ t) → M ⊫ R → GRealize sig M Pre R.
#sig #M #Pre #R #HT #HW #t #HPre cases (HT … t HPre) #i * #outc #Hloop 
@(ex_intro … i) @(ex_intro … outc) % // @(HW … i) //
qed.

lemma Realize_to_GRealize : ∀sig.∀M: mTM sig.∀P,R. 
  M ⊨ R → GRealize sig M P R.
#alpha #M #Pre #R #HR #t #HPre
cases (HR t) -HR #k * #outc * #Hloop #HR 
@(ex_intro ?? k) @(ex_intro ?? outc) % 
  [ @Hloop | @HR ]
qed.

lemma acc_Realize_to_acc_GRealize: ∀sig.∀M:mTM sig.∀q:states sig M.∀P,R1,R2. 
  M ⊨ [q:R1,R2] → accGRealize sig M q P R1 R2.
#alpha #M #q #Pre #R1 #R2 #HR #t #HPre
cases (HR t) -HR #k * #outc * * #Hloop #HRtrue #HRfalse 
@(ex_intro ?? k) @(ex_intro ?? outc) % 
  [ % [@Hloop] @HRtrue | @HRfalse]
qed.

(******************************** monotonicity ********************************)
lemma Realize_to_Realize : ∀sig.∀M:mTM sig.∀R1,R2.
  R1 ⊆ R2 → Realize sig M R1 → Realize sig M R2.
#alpha #M #R1 #R2 #Himpl #HR1 #intape
cases (HR1 intape) -HR1 #k * #outc * #Hloop #HR1
@(ex_intro ?? k) @(ex_intro ?? outc) % /2/
qed.

lemma WRealize_to_WRealize: ∀sig.∀M:mTM sig.∀R1,R2.
  R1 ⊆ R2 → WRealize sig M R1 → WRealize ? M R2.
#alpha #M #R1 #R2 #Hsub #HR1 #intape #i #outc #Hloop
@Hsub @(HR1 … i) @Hloop
qed.

lemma GRealize_to_GRealize : ∀sig.∀M:mTM sig.∀P,R1,R2.
  R1 ⊆ R2 → GRealize sig M P R1 → GRealize sig M P R2.
#alpha #M #P #R1 #R2 #Himpl #HR1 #intape #HP
cases (HR1 intape HP) -HR1 #k * #outc * #Hloop #HR1
@(ex_intro ?? k) @(ex_intro ?? outc) % /2/
qed.

lemma GRealize_to_GRealize_2 : ∀sig.∀M:mTM sig.∀P1,P2,R1,R2.
  P2 ⊆ P1 → R1 ⊆ R2 → GRealize sig M P1 R1 → GRealize sig M P2 R2.
#alpha #M #P1 #P2 #R1 #R2 #Himpl1 #Himpl2 #H1 #intape #HP
cases (H1 intape (Himpl1 … HP)) -H1 #k * #outc * #Hloop #H1
@(ex_intro ?? k) @(ex_intro ?? outc) % /2/
qed.

lemma acc_Realize_to_acc_Realize: ∀sig.∀M:mTM sig.∀q:states sig M.∀R1,R2,R3,R4. 
  R1 ⊆ R3 → R2 ⊆ R4 → M ⊨ [q:R1,R2] → M ⊨ [q:R3,R4].
#alpha #M #q #R1 #R2 #R3 #R4 #Hsub13 #Hsub24 #HRa #intape
cases (HRa intape) -HRa #k * #outc * * #Hloop #HRtrue #HRfalse 
@(ex_intro ?? k) @(ex_intro ?? outc) % 
  [ % [@Hloop] #Hq @Hsub13 @HRtrue // | #Hq @Hsub24 @HRfalse //]
qed.

(**************************** A canonical relation ****************************)

definition R_mTM ≝ λsig.λM:mTM sig.λq.λt1,t2.
∃i,outc.
  loopM ? M i (mk_mconfig ??? q t1) = Some ? outc ∧ 
  t2 = (ctapes ??? outc).
  
lemma R_mTM_to_R: ∀sig.∀M:mTM sig.∀R. ∀t1,t2. 
  M ⊫ R → R_mTM ? M (start sig M) t1 t2 → R t1 t2.
#sig #M #R #t1 #t2 whd in ⊢ (%→?); #HMR * #i * #outc *
#Hloop #Ht2 >Ht2 @(HMR … Hloop)
qed.

(******************************** NOP Machine *********************************)

(* NO OPERATION
   t1 = t2 
  
definition nop_states ≝ initN 1.
definition start_nop : initN 1 ≝ mk_Sig ?? 0 (le_n … 1). *)

definition mnop ≝ 
  λalpha:FinSet.λn.mk_mTM alpha nop_states n
  (λp.let 〈q,a〉 ≝ p in 〈q,mk_Vector ? (S n) (make_list ? (None ?) (S n)) ?〉)
  start_nop (λ_.true).
elim n normalize //
qed.
  
definition R_mnop ≝ λalpha,n.λt1,t2:Vector (tape alpha) (S n).t2 = t1.

lemma sem_mnop :
  ∀alpha,n.mnop alpha n⊨ R_mnop alpha n.
#alpha #n #intapes @(ex_intro ?? 1) 
@(ex_intro … (mk_mconfig ??? start_nop intapes)) % % 
qed.

lemma mnop_single_state: ∀sig,n.∀q1,q2:states ? (mnop sig n). q1 = q2.
normalize #sig #n0 * #n #ltn1 * #m #ltm1 
generalize in match ltn1; generalize in match ltm1;
<(le_n_O_to_eq … (le_S_S_to_le … ltn1)) <(le_n_O_to_eq … (le_S_S_to_le … ltm1)) 
// qed.

(************************** Sequential Composition ****************************)

definition seq_trans ≝ λsig. λM1,M2 : TM sig. 
λp. let 〈s,a〉 ≝ p in
  match s with 
  [ inl s1 ⇒ 
      if halt sig M1 s1 then 〈inr … (start sig M2), None ?〉
      else let 〈news1,m〉 ≝ trans sig M1 〈s1,a〉 in 〈inl … news1,m〉
  | inr s2 ⇒ let 〈news2,m〉 ≝ trans sig M2 〈s2,a〉 in 〈inr … news2,m〉
  ].
 
definition seq ≝ λsig. λM1,M2 : TM sig. 
  mk_TM sig 
    (FinSum (states sig M1) (states sig M2))
    (seq_trans sig M1 M2) 
    (inl … (start sig M1))
    (λs.match s with 
      [ inl _ ⇒ false | inr s2 ⇒ halt sig M2 s2]). 

notation "a · b" right associative with precedence 65 for @{ 'middot $a $b}.
interpretation "sequential composition" 'middot a b = (seq ? a b).

definition lift_confL ≝ 
  λsig,S1,S2,c.match c with 
  [ mk_config s t ⇒ mk_config sig (FinSum S1 S2) (inl … s) t ].
  
definition lift_confR ≝ 
  λsig,S1,S2,c.match c with
  [ mk_config s t ⇒ mk_config sig (FinSum S1 S2) (inr … s) t ].
  
definition halt_liftL ≝ 
  λS1,S2,halt.λs:FinSum S1 S2.
  match s with
  [ inl s1 ⇒ halt s1
  | inr _ ⇒ true ]. (* should be vacuous in all cases we use halt_liftL *)

definition halt_liftR ≝ 
  λS1,S2,halt.λs:FinSum S1 S2.
  match s with
  [ inl _ ⇒ false 
  | inr s2 ⇒ halt s2 ].
      
lemma p_halt_liftL : ∀sig,S1,S2,halt,c.
  halt (cstate sig S1 c) =
     halt_liftL S1 S2 halt (cstate … (lift_confL … c)).
#sig #S1 #S2 #halt #c cases c #s #t %
qed.

lemma trans_seq_liftL : ∀sig,M1,M2,s,a,news,move.
  halt ? M1 s = false → 
  trans sig M1 〈s,a〉 = 〈news,move〉 → 
  trans sig (seq sig M1 M2) 〈inl … s,a〉 = 〈inl … news,move〉.
#sig (*#M1*) * #Q1 #T1 #init1 #halt1 #M2 #s #a #news #move
#Hhalt #Htrans whd in ⊢ (??%?); >Hhalt >Htrans %
qed.

lemma trans_seq_liftR : ∀sig,M1,M2,s,a,news,move.
  halt ? M2 s = false → 
  trans sig M2 〈s,a〉 = 〈news,move〉 → 
  trans sig (seq sig M1 M2) 〈inr … s,a〉 = 〈inr … news,move〉.
#sig #M1 * #Q2 #T2 #init2 #halt2 #s #a #news #move
#Hhalt #Htrans whd in ⊢ (??%?); >Hhalt >Htrans %
qed.

lemma step_seq_liftR : ∀sig,M1,M2,c0.
 halt ? M2 (cstate ?? c0) = false → 
 step sig (seq sig M1 M2) (lift_confR sig (states ? M1) (states ? M2) c0) =
 lift_confR sig (states ? M1) (states ? M2) (step sig M2 c0).
#sig #M1 (* * #Q1 #T1 #init1 #halt1 *) #M2 * #s #t
  lapply (refl ? (trans ?? 〈s,current sig t〉))
  cases (trans ?? 〈s,current sig t〉) in ⊢ (???% → %);
  #s0 #m0 cases t
  [ #Heq #Hhalt
  | 2,3: #s1 #l1 #Heq #Hhalt 
  |#ls #s1 #rs #Heq #Hhalt ]
  whd in ⊢ (???(????%)); >Heq whd in ⊢ (???%);
  whd in ⊢ (??(???%)?); whd in ⊢ (??%?); >(trans_seq_liftR … Heq) //
qed.

lemma step_seq_liftL : ∀sig,M1,M2,c0.
 halt ? M1 (cstate ?? c0) = false → 
 step sig (seq sig M1 M2) (lift_confL sig (states ? M1) (states ? M2) c0) =
 lift_confL sig ?? (step sig M1 c0).
#sig #M1 (* * #Q1 #T1 #init1 #halt1 *) #M2 * #s #t
  lapply (refl ? (trans ?? 〈s,current sig t〉))
  cases (trans ?? 〈s,current sig t〉) in ⊢ (???% → %);
  #s0 #m0 cases t
  [ #Heq #Hhalt
  | 2,3: #s1 #l1 #Heq #Hhalt 
  |#ls #s1 #rs #Heq #Hhalt ]
  whd in ⊢ (???(????%)); >Heq whd in ⊢ (???%);
  whd in ⊢ (??(???%)?); whd in ⊢ (??%?); >(trans_seq_liftL … Heq) //
qed.

lemma trans_liftL_true : ∀sig,M1,M2,s,a.
  halt ? M1 s = true → 
  trans sig (seq sig M1 M2) 〈inl … s,a〉 = 〈inr … (start ? M2),None ?〉.
#sig #M1 #M2 #s #a #Hhalt whd in ⊢ (??%?); >Hhalt %
qed.

lemma eq_ctape_lift_conf_L : ∀sig,S1,S2,outc.
  ctape sig (FinSum S1 S2) (lift_confL … outc) = ctape … outc.
#sig #S1 #S2 #outc cases outc #s #t %
qed.
  
lemma eq_ctape_lift_conf_R : ∀sig,S1,S2,outc.
  ctape sig (FinSum S1 S2) (lift_confR … outc) = ctape … outc.
#sig #S1 #S2 #outc cases outc #s #t %
qed.

theorem sem_seq: ∀sig.∀M1,M2:TM sig.∀R1,R2.
  M1 ⊨ R1 → M2 ⊨ R2 → M1 · M2 ⊨ R1 ∘ R2.
#sig #M1 #M2 #R1 #R2 #HR1 #HR2 #t 
cases (HR1 t) #k1 * #outc1 * #Hloop1 #HM1
cases (HR2 (ctape sig (states ? M1) outc1)) #k2 * #outc2 * #Hloop2 #HM2
@(ex_intro … (k1+k2)) @(ex_intro … (lift_confR … outc2))
%
[@(loop_merge ??????????? 
   (loop_lift ??? (lift_confL sig (states sig M1) (states sig M2))
   (step sig M1) (step sig (seq sig M1 M2)) 
   (λc.halt sig M1 (cstate … c)) 
   (λc.halt_liftL ?? (halt sig M1) (cstate … c)) … Hloop1))
  [ * *
   [ #sl #tl whd in ⊢ (??%? → ?); #Hl %
   | #sr #tr whd in ⊢ (??%? → ?); #Hr destruct (Hr) ]
  || #c0 #Hhalt <step_seq_liftL //
  | #x <p_halt_liftL %
  |6:cases outc1 #s1 #t1 %
  |7:@(loop_lift … (initc ?? (ctape … outc1)) … Hloop2) 
    [ * #s2 #t2 %
    | #c0 #Hhalt <step_seq_liftR // ]
  |whd in ⊢ (??(???%)?);whd in ⊢ (??%?);
   generalize in match Hloop1; cases outc1 #sc1 #tc1 #Hloop10 
   >(trans_liftL_true sig M1 M2 ??) 
    [ whd in ⊢ (??%?); whd in ⊢ (???%);
      @config_eq whd in ⊢ (???%); //
    | @(loop_Some ?????? Hloop10) ]
 ]
| @(ex_intro … (ctape ? (FinSum (states ? M1) (states ? M2)) (lift_confL … outc1)))
  % // >eq_ctape_lift_conf_L >eq_ctape_lift_conf_R //
]
qed.

theorem sem_seq_app: ∀sig.∀M1,M2:TM sig.∀R1,R2,R3.
  M1 ⊨ R1 → M2 ⊨ R2 → R1 ∘ R2 ⊆ R3 → M1 · M2 ⊨ R3.
#sig #M1 #M2 #R1 #R2 #R3 #HR1 #HR2 #Hsub
#t cases (sem_seq … HR1 HR2 t)
#k * #outc * #Hloop #Houtc @(ex_intro … k) @(ex_intro … outc)
% [@Hloop |@Hsub @Houtc]
qed.

(* composition with guards *)
theorem sem_seq_guarded: ∀sig.∀M1,M2:TM sig.∀Pre1,Pre2,R1,R2.
  GRealize sig M1 Pre1 R1 → GRealize sig M2 Pre2 R2 → 
  (∀t1,t2.Pre1 t1 → R1 t1 t2 → Pre2 t2) → 
  GRealize sig (M1 · M2) Pre1 (R1 ∘ R2).
#sig #M1 #M2 #Pre1 #Pre2 #R1 #R2 #HGR1 #HGR2 #Hinv #t1 #HPre1
cases (HGR1 t1 HPre1) #k1 * #outc1 * #Hloop1 #HM1
cases (HGR2 (ctape sig (states ? M1) outc1) ?) 
  [2: @(Hinv … HPre1 HM1)]  
#k2 * #outc2 * #Hloop2 #HM2
@(ex_intro … (k1+k2)) @(ex_intro … (lift_confR … outc2))
%
[@(loop_merge ??????????? 
   (loop_lift ??? (lift_confL sig (states sig M1) (states sig M2))
   (step sig M1) (step sig (seq sig M1 M2)) 
   (λc.halt sig M1 (cstate … c)) 
   (λc.halt_liftL ?? (halt sig M1) (cstate … c)) … Hloop1))
  [ * *
   [ #sl #tl whd in ⊢ (??%? → ?); #Hl %
   | #sr #tr whd in ⊢ (??%? → ?); #Hr destruct (Hr) ]
  || #c0 #Hhalt <step_seq_liftL //
  | #x <p_halt_liftL %
  |6:cases outc1 #s1 #t1 %
  |7:@(loop_lift … (initc ?? (ctape … outc1)) … Hloop2) 
    [ * #s2 #t2 %
    | #c0 #Hhalt <step_seq_liftR // ]
  |whd in ⊢ (??(???%)?);whd in ⊢ (??%?);
   generalize in match Hloop1; cases outc1 #sc1 #tc1 #Hloop10 
   >(trans_liftL_true sig M1 M2 ??) 
    [ whd in ⊢ (??%?); whd in ⊢ (???%);
      @config_eq whd in ⊢ (???%); //
    | @(loop_Some ?????? Hloop10) ]
 ]
| @(ex_intro … (ctape ? (FinSum (states ? M1) (states ? M2)) (lift_confL … outc1)))
  % // >eq_ctape_lift_conf_L >eq_ctape_lift_conf_R //
]
qed.

theorem sem_seq_app_guarded: ∀sig.∀M1,M2:TM sig.∀Pre1,Pre2,R1,R2,R3.
  GRealize sig M1 Pre1 R1 → GRealize sig M2 Pre2 R2 → 
  (∀t1,t2.Pre1 t1 → R1 t1 t2 → Pre2 t2) → R1 ∘ R2 ⊆ R3 →
  GRealize sig (M1 · M2) Pre1 R3.
#sig #M1 #M2 #Pre1 #Pre2 #R1 #R2 #R3 #HR1 #HR2 #Hinv #Hsub
#t #HPre1 cases (sem_seq_guarded … HR1 HR2 Hinv t HPre1)
#k * #outc * #Hloop #Houtc @(ex_intro … k) @(ex_intro … outc)
% [@Hloop |@Hsub @Houtc]
qed.








definition stop ≝ λsig.λM:TM sig.λc:config sig M.
  halt sig M (state sig M c).

let rec loop (A:Type[0]) n (f:A→A) p a on n ≝
  match n with 
  [ O ⇒ None ?
  | S m ⇒ if p a then (Some ? a) else loop A m f p (f a)
  ].

(* Compute ? M f states that f is computed by M *)
definition Compute ≝ λsig.λM:TM sig.λf:(list sig) → (list sig).
∀l.∃i.∃c.
  loop ? i (step sig M) (stop sig M) (init sig M l) = Some ? c ∧
  out ?? c = f l.

(* for decision problems, we accept a string if on termination
output is not empty *)

definition ComputeB ≝ λsig.λM:TM sig.λf:(list sig) → bool.
∀l.∃i.∃c.
  loop ? i (step sig M) (stop sig M) (init sig M l) = Some ? c ∧
  (isnilb ? (out ?? c) = false).

(* alternative approach.
We define the notion of computation. The notion must be constructive,
since we want to define functions over it, like lenght and size 

Perche' serve Type[2] se sposto a e b a destra? *)

inductive cmove (A:Type[0]) (f:A→A) (p:A →bool) (a,b:A): Type[0] ≝
  mk_move: p a = false → b = f a → cmove A f p a b.
  
inductive cstar (A:Type[0]) (M:A→A→Type[0]) : A →A → Type[0] ≝
| empty : ∀a. cstar A M a a
| more : ∀a,b,c. M a b → cstar A M b c → cstar A M a c.

definition computation ≝ λsig.λM:TM sig.
  cstar ? (cmove ? (step sig M) (stop sig M)).

definition Compute_expl ≝ λsig.λM:TM sig.λf:(list sig) → (list sig).
  ∀l.∃c.computation sig M (init sig M l) c → 
   (stop sig M c = true) ∧ out ?? c = f l.

definition ComputeB_expl ≝ λsig.λM:TM sig.λf:(list sig) → bool.
  ∀l.∃c.computation sig M (init sig M l) c → 
   (stop sig M c = true) ∧ (isnilb ? (out ?? c) = false).
 
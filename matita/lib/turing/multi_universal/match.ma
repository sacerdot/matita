(**************************************************************************)
(*       ___                                                              *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||         The HELM team.                                      *)
(*      ||A||         http://helm.cs.unibo.it                             *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU General Public License Version 2                  *)
(*                                                                        *)
(**************************************************************************)

include "turing/multi_universal/compare.ma".
include "turing/multi_universal/par_test.ma".


definition Rtc_multi_true ≝ 
  λalpha,test,n,i.λt1,t2:Vector ? (S n).
   (∃c. current alpha (nth i ? t1 (niltape ?)) = Some ? c ∧ test c = true) ∧ t2 = t1.
   
definition Rtc_multi_false ≝ 
  λalpha,test,n,i.λt1,t2:Vector ? (S n).
    (∀c. current alpha (nth i ? t1 (niltape ?)) = Some ? c → test c = false) ∧ t2 = t1.

lemma sem_test_char_multi :
  ∀alpha,test,n,i.i ≤ n → 
  inject_TM ? (test_char ? test) n i ⊨ 
  [ tc_true : Rtc_multi_true alpha test n i, Rtc_multi_false alpha test n i ].
#alpha #test #n #i #Hin #int
cases (acc_sem_inject … Hin (sem_test_char alpha test) int)
#k * #outc * * #Hloop #Htrue #Hfalse %{k} %{outc} % [ %
[ @Hloop
| #Hqtrue lapply (Htrue Hqtrue) * * * #c *
  #Hcur #Htestc #Hnth_i #Hnth_j %
  [ %{c} % //
  | @(eq_vec … (niltape ?)) #i0 #Hi0
    cases (decidable_eq_nat i0 i) #Hi0i
    [ >Hi0i @Hnth_i
    | @sym_eq @Hnth_j @sym_not_eq // ] ] ]
| #Hqfalse lapply (Hfalse Hqfalse) * * #Htestc #Hnth_i #Hnth_j %
  [ @Htestc
  | @(eq_vec … (niltape ?)) #i0 #Hi0
    cases (decidable_eq_nat i0 i) #Hi0i
    [ >Hi0i @Hnth_i
    | @sym_eq @Hnth_j @sym_not_eq // ] ] ]
qed.

definition Rm_test_null_true ≝ 
  λalpha,n,i.λt1,t2:Vector ? (S n).
   current alpha (nth i ? t1 (niltape ?)) ≠ None ? ∧ t2 = t1.
   
definition Rm_test_null_false ≝ 
  λalpha,n,i.λt1,t2:Vector ? (S n).
    current alpha (nth i ? t1 (niltape ?)) = None ? ∧ t2 = t1.

lemma sem_test_null_multi : ∀alpha,n,i.i ≤ n → 
  inject_TM ? (test_null ?) n i ⊨ 
    [ tc_true : Rm_test_null_true alpha n i, Rm_test_null_false alpha n i ].
#alpha #n #i #Hin #int
cases (acc_sem_inject … Hin (sem_test_null alpha) int)
#k * #outc * * #Hloop #Htrue #Hfalse %{k} %{outc} % [ %
[ @Hloop
| #Hqtrue lapply (Htrue Hqtrue) * * #Hcur #Hnth_i #Hnth_j % //
  @(eq_vec … (niltape ?)) #i0 #Hi0 cases (decidable_eq_nat i0 i) #Hi0i
  [ >Hi0i @sym_eq @Hnth_i | @sym_eq @Hnth_j @sym_not_eq // ] ] 
| #Hqfalse lapply (Hfalse Hqfalse) * * #Hcur #Hnth_i #Hnth_j %
  [ @Hcur
  | @(eq_vec … (niltape ?)) #i0 #Hi0 cases (decidable_eq_nat i0 i) // 
    #Hi0i @sym_eq @Hnth_j @sym_not_eq // ] ] 
qed.

lemma comp_list: ∀S:DeqSet. ∀l1,l2:list S.∀is_endc. ∃l,tl1,tl2. 
  l1 = l@tl1 ∧ l2 = l@tl2 ∧ (∀c.c ∈ l = true → is_endc c = false) ∧
  ∀a,tla. tl1 = a::tla → 
  is_endc a = true ∨ (is_endc a = false ∧∀b,tlb.tl2 = b::tlb → a≠b).
#S #l1 #l2 #is_endc elim l1 in l2;
[ #l2 %{[ ]} %{[ ]} %{l2} normalize %
  [ % [ % // | #c #H destruct (H) ] | #a #tla #H destruct (H) ]
| #x #l3 #IH cases (true_or_false (is_endc x)) #Hendcx
  [ #l %{[ ]} %{(x::l3)} %{l} normalize
    % [ % [ % // | #c #H destruct (H) ] | #a #tla #H destruct (H) >Hendcx % % ]
  | *
    [ %{[ ]} %{(x::l3)} %{[ ]} normalize %
      [ % [ % // | #c #H destruct (H) ]
      | #a #tla #H destruct (H) cases (is_endc a)
        [ % % | %2 % // #b #tlb #H destruct (H) ]
      ]
    | #y #l4 cases (true_or_false (x==y)) #Hxy
      [ lapply (\P Hxy) -Hxy #Hxy destruct (Hxy)  
        cases (IH l4) -IH #l * #tl1 * #tl2 * * * #Hl3 #Hl4 #Hl #IH
        %{(y::l)} %{tl1} %{tl2} normalize
        % [ % [ % // 
              | #c cases (true_or_false (c==y)) #Hcy >Hcy normalize
                [ >(\P Hcy) //
                | @Hl ]
              ]
          | #a #tla #Htl1 @(IH … Htl1) ]
      | %{[ ]} %{(x::l3)} %{(y::l4)} normalize %
        [ % [ % // | #c #H destruct (H) ]
        | #a #tla #H destruct (H) cases (is_endc a)
          [ % % | %2 % // #b #tlb #H destruct (H) @(\Pf Hxy) ]
        ]
      ]
    ]
  ]
]
qed.        
  
axiom daemon : ∀X:Prop.X.

definition match_test ≝ λsrc,dst.λsig:DeqSet.λn,is_endc.λv:Vector ? n.
  match (nth src (option sig) v (None ?)) with 
  [ None ⇒  false 
  | Some x ⇒  notb ((is_endc x) ∨ (nth dst (DeqOption sig) v (None ?) == None ?))]. 

definition match_step ≝ λsrc,dst,sig,n,is_startc,is_endc.
  compare src dst sig n is_endc ·
     (ifTM ?? (partest sig n (match_test src dst sig ? is_endc))
      (single_finalTM ??
        (parmove src dst sig n L is_startc · (inject_TM ? (move_r ?) n dst)))
      (nop …)
      partest1).
      
definition R_match_step_false ≝ 
  λsrc,dst,sig,n,is_endc.λint,outt: Vector (tape sig) (S n).
  ∀ls,x,xs,end,rs.
  nth src ? int (niltape ?) = midtape sig ls x (xs@end::rs) →
  (∀c0. memb ? c0 (x::xs) = true → is_endc c0 = false) → is_endc end = true →
   ((current sig (nth dst (tape sig) int (niltape sig)) = None ?) ∧ outt = int) ∨
    (∃ls0,rs0,xs0. nth dst ? int (niltape ?) = midtape sig ls0 x rs0 ∧
      xs = rs0@xs0 ∧
      current sig (nth dst (tape sig) outt (niltape sig)) = None ?) ∨
    (∃ls0,rs0. 
     nth dst ? int (niltape ?) = midtape sig ls0 x (xs@rs0) ∧
     ∀rsj,c. 
     rs0 = c::rsj →
     outt = change_vec ??
            (change_vec ?? int (midtape sig (reverse ? xs@x::ls) end rs) src)
            (midtape sig (reverse ? xs@x::ls0) c rsj) dst).

definition R_match_step_true ≝ 
  λsrc,dst,sig,n,is_startc,is_endc.λint,outt: Vector (tape sig) (S n).
  ∀s.current sig (nth src (tape sig) int (niltape sig)) = Some ? s → 
  current sig (nth dst (tape sig) int (niltape sig)) ≠ None ? ∧
  (is_startc s = true → 
   (∀c.c ∈ right ? (nth src (tape sig) int (niltape sig)) = true → is_startc c = false) →
   (∀s1.current sig (nth dst (tape sig) int (niltape sig)) = Some ? s1 → s ≠ s1 →  
    outt = change_vec ?? int 
          (tape_move … (nth dst ? int (niltape ?)) (Some ? 〈s1,R〉)) dst ∧ is_endc s = false) ∧  
   (∀ls,x,xs,ci,cj,rs,ls0,rs0. 
     nth src ? int (niltape ?) = midtape sig ls x (xs@ci::rs) →
     nth dst ? int (niltape ?) = midtape sig ls0 x (xs@cj::rs0) →
     (∀c0. memb ? c0 (x::xs) = true → is_endc c0 = false) → 
      ci ≠ cj →
      (outt = change_vec ?? int 
          (tape_move … (nth dst ? int (niltape ?)) (Some ? 〈x,R〉)) dst ∧ is_endc ci = false))). 
(*    ∧
    (rs0 = [ ] →
     outt = change_vec ??
           (change_vec ?? int (midtape sig (reverse ? xs@x::ls) ci rs) src)
           (mk_tape sig (reverse ? xs@x::ls0) (None ?) [ ]) dst)). *)
           
lemma sem_match_step :
  ∀src,dst,sig,n,is_startc,is_endc.src ≠ dst → src < S n → dst < S n → 
  match_step src dst sig n is_startc is_endc ⊨ 
    [ inr ?? (inr ?? (inl … (inr ?? start_nop))) : 
      R_match_step_true src dst sig n is_startc is_endc, 
      R_match_step_false src dst sig n is_endc ].
#src #dst #sig #n #is_startc #is_endc #Hneq #Hsrc #Hdst 
@(acc_sem_seq_app sig n … (sem_compare src dst sig n is_endc Hneq Hsrc Hdst)
    (acc_sem_if ? n … (sem_partest sig n (match_test src dst sig ? is_endc))
      (sem_seq … 
        (sem_parmoveL ???? is_startc Hneq Hsrc Hdst) 
        (sem_inject … dst (le_S_S_to_le … Hdst) (sem_move_r ? )))
      (sem_nop …)))
[#ta #tb #tc * #Hcomp1 #Hcomp2 * #td * * #Htest #Htd >Htd -Htd
 * #te * #Hte #Htb whd 
 #s #Hcurta_src % 
 [ lapply (refl ? (current ? (nth dst ? ta (niltape ?)))) 
   cases (current ? (nth dst ? ta (niltape ?))) in ⊢ (???%→%);
   [| #c #_ % #Hfalse destruct (Hfalse) ]
   #Hcurta_dst >Hcomp1 in Htest; [| %2 %2 //]
   whd in ⊢ (??%?→?); change with (current ? (niltape ?)) in match (None ?);
    <nth_vec_map >Hcurta_src whd in ⊢ (??%?→?); <nth_vec_map
    >Hcurta_dst cases (is_endc s) normalize in ⊢ (%→?); #H destruct (H)
 | #Hstart #Hnotstart %
   [ #s1 #Hcurta_dst #Hneqss1 -Hcomp2
     cut (tc = ta) 
     [@Hcomp1 %2 %1 %1 >Hcurta_src >Hcurta_dst @(not_to_not … Hneqss1) #H destruct (H) //] 
     #H destruct (H) -Hcomp1 cases Hte #_ -Hte #Hte
     cut (te = ta) [@Hte %1 %1 %{s} % //] -Hte #H destruct (H) %
     [cases Htb * #_ #Hmove #Hmove1 @(eq_vec … (niltape … ))
      #i #Hi cases (decidable_eq_nat i dst) #Hidst
       [ >Hidst >nth_change_vec // cases (current_to_midtape … Hcurta_dst)
         #ls * #rs #Hta_mid >(Hmove … Hta_mid) >Hta_mid cases rs //
       | >nth_change_vec_neq [|@sym_not_eq //] @sym_eq @Hmove1 @sym_not_eq // ]
     | whd in Htest:(??%?); >(nth_vec_map ?? (current sig)) in Hcurta_src; #Hcurta_src
       >Hcurta_src in Htest; whd in ⊢ (??%?→?);
       cases (is_endc s) // whd in ⊢ (??%?→?); #H @sym_eq // 
     ]
   |#ls #x #xs #ci #cj #rs #ls0 #rs00 #Htasrc_mid #Htadst_mid #Hnotendc #Hcicj 
    cases (Hcomp2 … Htasrc_mid Htadst_mid Hnotendc) [ * #H destruct (H) ]
    * #cj' * #rs0' * #Hcjrs0 destruct (Hcjrs0) -Hcomp2 #Hcomp2
    lapply (Hcomp2 (or_intror ?? Hcicj)) -Hcomp2 #Htc %
    [ cases Hte -Hte #Hte #_ whd in Hte;
      >Htasrc_mid in Hcurta_src; whd in ⊢ (??%?→?); #H destruct (H) 
      lapply (Hte ls ci (reverse ? xs) rs s ??? ls0 cj' (reverse ? xs) s rs0' (refl ??) ?) //
      [ >Htc >nth_change_vec //
      | #c0 #Hc0 @(Hnotstart c0) >Htasrc_mid cases (orb_true_l … Hc0) -Hc0 #Hc0
        [@memb_append_l2 >(\P Hc0) @memb_hd
        |@memb_append_l1 <(reverse_reverse …xs) @memb_reverse //
        ]
      | >Htc >change_vec_commute // >nth_change_vec // ] -Hte
      >Htc >change_vec_commute // >change_vec_change_vec 
      >change_vec_commute [|@sym_not_eq //] >change_vec_change_vec #Hte
      >Hte in Htb; * * #_ >reverse_reverse #Htbdst1 #Htbdst2 -Hte @(eq_vec … (niltape ?))
      #i #Hi cases (decidable_eq_nat i dst) #Hidst
      [ >Hidst >nth_change_vec // >(Htbdst1 ls0 s (xs@cj'::rs0'))
        [| >nth_change_vec // ]
        >Htadst_mid cases xs //
      | >nth_change_vec_neq [|@sym_not_eq // ]
        <Htbdst2 [| @sym_not_eq // ] >nth_change_vec_neq [| @sym_not_eq // ]
        <Htasrc_mid >change_vec_same % ]
    | >Hcurta_src in Htest; whd in ⊢(??%?→?);
      >Htc >change_vec_commute //
      change with (current ? (niltape ?)) in match (None ?);
      <nth_vec_map >nth_change_vec // whd in ⊢ (??%?→?);
      cases (is_endc ci) whd in ⊢ (??%?→?); #H destruct (H) % 
    ]
   ]
  ]
|#intape #outtape #ta * #Hcomp1 #Hcomp2 * #tb * * #Hc #Htb 
 whd in ⊢ (%→?); #Hout >Hout >Htb whd
 #ls #c_src #xs #end #rs #Hmid_src #Hnotend #Hend
 lapply (current_to_midtape sig (nth dst ? intape (niltape ?)))
 cases (current … (nth dst ? intape (niltape ?))) in Hcomp1;
  [#Hcomp1 #_ %1 % % [% | @Hcomp1 %2 %2 % ]
  |#c_dst cases (true_or_false (c_src == c_dst)) #Hceq
    [#_ #Hmid_dst cases (Hmid_dst c_dst (refl …)) -Hmid_dst
     #ls_dst * #rs_dst #Hmid_dst
     cases (comp_list … (xs@end::rs) rs_dst is_endc) #xs1 * #rsi * #rsj * * * 
     #Hrs_src #Hrs_dst #Hnotendxs1 #Hneq >Hrs_dst in Hmid_dst; #Hmid_dst
     cut (∃r1,rs1.rsi = r1::rs1) [@daemon] * #r1 * #rs1 #Hrs1 >Hrs1 in Hrs_src;
     #Hrs_src >Hrs_src in Hmid_src; #Hmid_src <(\P Hceq) in Hmid_dst; #Hmid_dst
     lapply (Hcomp2 ??????? Hmid_src Hmid_dst ?) 
     [ #c0 #Hc0 cases (orb_true_l … Hc0) -Hc0 #Hc0
       [ >(\P Hc0) @Hnotend @memb_hd | @Hnotendxs1 //] ] 
     *
     [ * #Hrsj >Hrsj #Hta % %2 >Hta >nth_change_vec //
       %{ls_dst} %{xs1} cut (∃xs0.xs = xs1@xs0)
       [lapply Hnotendxs1 -Hnotendxs1 lapply Hrs_src lapply xs elim xs1
         [ #l #_ #_ %{l} %
         | #x2 #xs2 #IH * 
           [ whd in ⊢ (??%%→?); #H destruct (H) #Hnotendxs2
             >Hnotendxs2 in Hend; [ #H destruct (H) |@memb_hd ]
           | #x2' #xs2' whd in ⊢ (??%%→?); #H destruct (H)
             #Hnotendxs2 cases (IH xs2' e0 ?)
             [ #xs0 #Hxs2 %{xs0} @eq_f //
             |#c #Hc @Hnotendxs2 @memb_cons // ]
           ]
         ] 
       ] * #xs0 #Hxs0 %{xs0} % [ %
       [ >Hmid_dst >Hrsj >append_nil %
       | @Hxs0 ]
       | cases (reverse ? xs1) // ]
     | * #cj * #rs2 * #Hrsj #Hta lapply (Hta ?)
       [ cases (Hneq ?? Hrs1) /2/ * #_ #Hr1 %2 @(Hr1 ?? Hrsj) ] -Hta #Hta
       %2 >Hta in Hc; whd in ⊢ (??%?→?);
       change with (current ? (niltape ?)) in match (None ?);
       <nth_vec_map >nth_change_vec_neq [|@sym_not_eq //] >nth_change_vec //
       whd in ⊢ (??%?→?); #Hc cut (is_endc r1 = true)
       [ cases (is_endc r1) in Hc; whd in ⊢ (??%?→?); //
         change with (current ? (niltape ?)) in match (None ?);
         <nth_vec_map >nth_change_vec // normalize #H destruct (H) ]
       #Hendr1 cut (xs = xs1)
       [ lapply Hnotendxs1 lapply Hnotend lapply Hrs_src lapply xs1
         -Hnotendxs1 -Hnotend -Hrs_src -xs1 elim xs
         [ * normalize in ⊢ (%→?); //
           #x2 #xs2 normalize in ⊢ (%→?); #Heq destruct (Heq) #_ #Hnotendxs1
           lapply (Hnotendxs1 ? (memb_hd …)) >Hend #H destruct (H)
         | #x2 #xs2 #IH *
           [ normalize in ⊢ (%→?); #Heq destruct (Heq) #Hnotendc
             >Hnotendc in Hendr1; [| @memb_cons @memb_hd ]
             normalize in ⊢ (%→?); #H destruct (H)
           | #x3 #xs3 normalize in ⊢ (%→?); #Heq destruct (Heq)
             #Hnotendc #Hnotendcxs1 @eq_f @IH
             [ @(cons_injective_r … Heq)
             | #c0 #Hc0 @Hnotendc cases (orb_true_l … Hc0) -Hc0 #Hc0
               [ >(\P Hc0) @memb_hd
               | @memb_cons @memb_cons // ]
             | #c #Hc @Hnotendcxs1 @memb_cons // ]
           ]
         ]
       | #Hxsxs1 destruct (Hxsxs1) >Hmid_dst %{ls_dst} %{rsj} % //
         #rsj0 #c >Hrsj #Hrsj0 destruct (Hrsj0) 
         lapply (append_l2_injective … Hrs_src) // #Hrs' destruct (Hrs') %
       ]
     ]
    |#Hcomp1 #Hsrc cases (Hsrc ? (refl ??)) -Hsrc #ls0 * #rs0 #Hdst 
     @False_ind lapply (Hcomp1 ?) [%2 %1 %1 >Hmid_src normalize
     @(not_to_not ??? (\Pf Hceq)) #H destruct //] #Hintape >Hintape in Hc;
     whd in ⊢(??%?→?); >Hmid_src  
     change with (current ? (niltape ?)) in match (None ?);
     <nth_vec_map >Hmid_src whd in ⊢ (??%?→?);
     >(Hnotend c_src) [|@memb_hd]
     change with (current ? (niltape ?)) in match (None ?);
     <nth_vec_map >Hmid_src whd in ⊢ (??%?→?); >Hdst normalize #H destruct (H)
   ]
  ]
]
qed.

definition match_m ≝ λsrc,dst,sig,n,is_startc,is_endc.
  whileTM … (match_step src dst sig n is_startc is_endc) 
    (inr ?? (inr ?? (inl … (inr ?? start_nop)))).

definition R_match_m ≝ 
  λsrc,dst,sig,n,is_startc,is_endc.λint,outt: Vector (tape sig) (S n).
(*  (current sig (nth dst (tape sig) int (niltape sig)) = None ? → outt = int) ∧ *)
  ∀ls,x,xs,end,rs.
  nth src ? int (niltape ?) = midtape sig ls x (xs@end::rs) →
  (∀c0. memb ? c0 (x::xs) = true → is_endc c0 = false) → is_endc end = true →
  (∀c0. memb ? c0 (xs@end::rs) = true → is_startc c0 = false) → 
  (current sig (nth dst (tape sig) int (niltape sig)) = None ? → outt = int) ∧
  (is_startc x = true →
   (∀ls0,x0,rs0.
    nth dst ? int (niltape ?) = midtape sig ls0 x0 rs0 →
    (∃l,l1.x0::rs0 = l@x::xs@l1 ∧
     ∀cj,l2.l1=cj::l2 →
     outt = change_vec ?? 
            (change_vec ?? int (midtape sig (reverse ? xs@x::ls) end rs) src)
            (midtape sig ((reverse ? (l@x::xs))@ls0) cj l2) dst) ∨
    ∀l,l1.x0::rs0 ≠ l@x::xs@l1)).

(*
definition R_match_m ≝ 
  λi,j,sig,n,is_startc,is_endc.λint,outt: Vector (tape sig) (S n).
  (((∃x.current ? (nth i ? int (niltape ?)) = Some ? x ∧ is_endc x = true) ∨
    current ? (nth i ? int (niltape ?)) = None ? ∨
    current ? (nth j ? int (niltape ?)) = None ?) → outt = int) ∧
  (∀ls,x,xs,ci,rs,ls0,x0,rs0.
    (∀x. is_startc x ≠ is_endc x) → 
    is_startc x = true → is_endc ci = true → 
    (∀z. memb ? z (x::xs) = true → is_endc x = false) →
    nth i ? int (niltape ?) = midtape sig ls x (xs@ci::rs) →
    nth j ? int (niltape ?) = midtape sig ls0 x0 rs0 →
    (∃l,l1.x0::rs0 = l@x::xs@l1 ∧
     ∀cj,l2.l1=cj::l2 →
     outt = change_vec ?? 
            (change_vec ?? int (midtape sig (reverse ? xs@x::ls) ci rs) i)
            (midtape sig ((reverse ? (l@x::xs))@ls0) cj l2) j) ∨
    ∀l,l1.x0::rs0 ≠ l@x::xs@l1).
*)

(*
axiom sub_list_dec: ∀A.∀l,ls:list A. 
  ∃l1,l2. l = l1@ls@l2 ∨ ∀l1,l2. l ≠ l1@ls@l2.
*)

lemma not_sub_list_merge : 
  ∀T.∀a,b:list T. (∀l1.a ≠ b@l1) → (∀t,l,l1.a ≠ t::l@b@l1) → ∀l,l1.a ≠ l@b@l1.
#T #a #b #H1 #H2 #l elim l normalize //
qed.

lemma not_sub_list_merge_2 : 
  ∀T:DeqSet.∀a,b:list T.∀t. (∀l1.t::a ≠ b@l1) → (∀l,l1.a ≠ l@b@l1) → ∀l,l1.t::a ≠ l@b@l1.
#T #a #b #t #H1 #H2 #l elim l //
#t0 #l1 #IH #l2 cases (true_or_false (t == t0)) #Htt0
[ >(\P Htt0) % normalize #H destruct (H) cases (H2 l1 l2) /2/
| normalize % #H destruct (H) cases (\Pf Htt0) /2/ ]
qed.


lemma wsem_match_m : ∀src,dst,sig,n,is_startc,is_endc.
src ≠ dst → src < S n → dst < S n → 
  match_m src dst sig n is_startc is_endc ⊫ R_match_m src dst sig n is_startc is_endc.
#src #dst #sig #n #is_startc #is_endc #Hneq #Hsrc #Hdst #ta #k #outc #Hloop
lapply (sem_while … (sem_match_step src dst sig n is_startc is_endc Hneq Hsrc Hdst) … Hloop) //
-Hloop * #tb * #Hstar @(star_ind_l ??????? Hstar) -Hstar
[ #tc #Hfalse #ls #x #xs #end #rs #Hmid_src #Hnotend #Hend #Hnotstart
  cases (Hfalse … Hmid_src Hnotend Hend) -Hfalse 
  [(* current dest = None *) *
    [ * #Hcur_dst #Houtc %
      [#_ >Houtc //
      |#Hstart #ls0 #x0 #rs0 #Hmid_dst >Hmid_dst in Hcur_dst; 
       normalize in ⊢ (%→?); #H destruct (H)
      ]
    | * #ls0 * #rs0 * #xs0 * * #Htc_dst #Hrs0 #HNone %
      [ >Htc_dst normalize in ⊢ (%→?); #H destruct (H)
      | #Hstart #ls1 #x1 #rs1 >Htc_dst #H destruct (H)
        >Hrs0 cases xs0
        [ % %{[ ]} %{[ ]} % [ >append_nil >append_nil %]
          #cj #ls2 #H destruct (H)
        | #x2 #xs2 %2 #l #l1 % #Habs lapply (eq_f ?? (length ?) ?? Habs)
          >length_append whd in ⊢ (??%(??%)→?); >length_append
          >length_append normalize >commutative_plus whd in ⊢ (???%→?);
          #H destruct (H) lapply e0 >(plus_n_O (|rs1|)) in ⊢ (??%?→?);
          >associative_plus >associative_plus 
          #e1 lapply (injective_plus_r ??? e1) whd in ⊢ (???%→?);
          #e2 destruct (e2)
        ]
      ]
    ]
  |* #ls0 * #rs0 * #Hmid_dst #HFalse %
    [ >Hmid_dst normalize in ⊢ (%→?); #H destruct (H)
    | #Hstart #ls1 #x1 #rs1 >Hmid_dst #H destruct (H)
     %1 %{[ ]} %{rs0} % [%] #cj #l2 #Hnotnil 
     >reverse_cons >associative_append @(HFalse ?? Hnotnil)
    ]
  ]
|#ta #tb #tc #Htrue #Hstar #IH #Hout lapply (IH Hout) -IH -Hout #IH whd
 #ls #x #xs #end #rs #Hmid_src #Hnotend #Hend #Hnotstart 
 lapply (refl ? (current ? (nth dst ? ta (niltape ?))))
 cases (current ? (nth dst ? ta (niltape ?))) in ⊢ (???%→?); 
  [#Hmid_dst % 
    [#_ whd in Htrue; >Hmid_src in Htrue; #Htrue
     cases (Htrue x (refl … )) -Htrue * #Htaneq #_
     @False_ind >Hmid_dst in Htaneq; /2/
    |#Hstart #ls0 #x0 #rs0 #Hmid_dst2 >Hmid_dst2 in Hmid_dst; normalize in ⊢ (%→?); 
     #H destruct (H)
    ]
  | #c #Hcurta_dst % [ >Hcurta_dst #H destruct (H) ]
    #Hstart #ls0 #x0 #rs0 #Hmid_dst >Hmid_dst in Hcurta_dst; normalize in ⊢ (%→?);
    #H destruct (H) whd in Htrue; >Hmid_src in Htrue; #Htrue
    cases (Htrue x (refl …)) -Htrue #_ #Htrue cases (Htrue Hstart Hnotstart) -Htrue
    cases (true_or_false (x==c)) #eqx
    [ lapply (\P eqx) -eqx #eqx destruct (eqx)
      #_ #Htrue cases (comp_list ? (xs@end::rs) rs0 is_endc)
      #x1 * #tl1 * #tl2 * * * #Hxs #Hrs0 #Hnotendx1
      cases tl1 in Hxs; 
      [>append_nil #Hx1 <Hx1 in Hnotendx1; #Hnotendx1
       lapply (Hnotendx1 end ?) [ @memb_append_l2 @memb_hd ]
       >Hend #H destruct (H) ]
      #ci -tl1 #tl1 #Hxs #H cases (H … (refl … ))
      [ #Hendci % cases (IH ????? Hmid_src Hnotend Hend Hnotstart)
      (* this is absurd, since Htrue conlcudes is_endc ci =false *)
       (* no, è più complicato
       #Hend_ci lapply (Htrue ls c xi
       *)
        @daemon (* lapply(Htrue … (refl …)) -Htrue *)
      |cases tl2 in Hrs0;
        [ >append_nil #Hrs0 destruct (Hrs0) * #Hcifalse#_ %2
          cut (∃l.xs = x1@ci::l) 
          [lapply Hxs lapply Hnotendx1 lapply Hnotend lapply xs 
           -Hxs -xs -Hnotendx1 elim x1
            [ *
              [ #_ #_ normalize #H1 destruct (H1) >Hend in Hcifalse;
                #H1 destruct (H1)
              | #x2 #xs2 #_ #_ normalize #H >(cons_injective_l ????? H) %{xs2} % ]
            | #x2 #xs2 #IHin *
              [ #_ #Hnotendxs2 normalize #H destruct (H) 
                >(Hnotendxs2 ? (memb_hd …)) in Hend; #H destruct (H)
              | #x3 #xs3 #Hnotendxs3 #Hnotendxs2 normalize #H destruct (H)
                cases (IHin ??? e0)
                [ #xs4 #Hxs4 >Hxs4 %{xs4} %
                | #c0 #Hc0 cases (orb_true_l … Hc0) -Hc0 #Hc0
                  [ >(\P Hc0) @Hnotendxs3 @memb_hd
                  | @Hnotendxs3 @memb_cons @memb_cons @Hc0 ]
                | #c0 #Hc0 @Hnotendxs2 @memb_cons @Hc0 ]
              ]
            ]
          ] * #l #Hxs' >Hxs'
          #l0 #l1 % #H lapply (eq_f ?? (length ?) ?? H) -H
          >length_append normalize >length_append >length_append
          normalize >commutative_plus normalize #H destruct (H) -H
          >associative_plus in e0; >associative_plus
          >(plus_n_O (|x1|)) in ⊢(??%?→?); #H lapply (injective_plus_r … H)
          -H normalize #H destruct (H)
        | #cj #tl2' #Hrs0 * #Hcifalse #Hcomp lapply (Htrue ls c x1 ci cj tl1 ls0 tl2' ????)
          [ @(Hcomp ?? (refl ??))
          | #c0 #Hc0 cases (orb_true_l … Hc0) #Hc0
            [ @Hnotend >(\P Hc0) @memb_hd
            | @Hnotendx1 // ]
          | >Hmid_dst >Hrs0 %
          | >Hxs %
          | * #Htb >Htb #Hendci >Hrs0 >Hxs
            cases (IH ls c xs end rs ? Hnotend Hend Hnotstart) -IH 
            [| >Htb >nth_change_vec_neq [|@sym_not_eq //] @Hmid_src ]
            #_ #IH lapply Hxs lapply Hnotendx1 -Hxs -Hnotendx1 cases x1 in Hrs0;
            [ #Hrs0 #_ whd in ⊢ (???%→?); #Hxs
              cases (IH Hstart (c::ls0) cj tl2' ?)
              [ -IH * #l * #l1 * #Hll1 #IH % %{(c::l)} %{l1} 
                % [ @eq_f @Hll1 ]
                #cj0 #l2 #Hcj0 >(IH … Hcj0) >Htb
                >change_vec_commute // >change_vec_change_vec
                >change_vec_commute [|@sym_not_eq // ] @eq_f3 //
                >reverse_cons >associative_append %
              | #IH %2 #l #l1 >(?:l@c::xs@l1 = l@(c::xs)@l1) [|%]
                @not_sub_list_merge
                [ #l2 cut (∃xs'.xs = ci::xs')
                  [ cases xs in Hxs;
                    [ normalize #H destruct (H) >Hend in Hendci; #H destruct (H)
                    | #ci' #xs' normalize #H lapply (cons_injective_l ????? H)
                      #H1 >H1 %{xs'} % ]
                  ]
                  * #xs' #Hxs' >Hxs' normalize % #H destruct (H)
                  lapply (Hcomp … (refl ??)) * /2/
                |#t #l2 #l3 % normalize #H lapply (cons_injective_r ????? H)
                 -H #H >H in IH; #IH cases (IH l2 l3) -IH #IH @IH % ] 
              | >Htb >nth_change_vec // >Hmid_dst >Hrs0 % ]
            | #x2 #xs2 normalize in ⊢ (%→?); #Hrs0 #Hnotendxs2 normalize in ⊢ (%→?);
              #Hxs cases (IH Hstart (c::ls0) x2 (xs2@cj::tl2') ?)
              [ -IH * #l * #l1 * #Hll1 #IH % %{(c::l)} %{l1} 
                % [ @eq_f @Hll1 ]
                #cj0 #l2 #Hcj0 >(IH … Hcj0) >Htb
                >change_vec_commute // >change_vec_change_vec
                >change_vec_commute [|@sym_not_eq // ] @eq_f3 //
                >reverse_cons >associative_append %
              | -IH #IH %2 #l #l1 >(?:l@c::xs@l1 = l@(c::xs)@l1) [|%] 
                @not_sub_list_merge_2 [| @IH]
                cut (∃l2.xs = (x2::xs2)@ci::l2)
                [lapply Hnotendxs2
                 lapply Hnotend -Hnotend lapply Hxs
                 >(?:x2::xs2@ci::tl1 = (x2::xs2)@ci::tl1) [|%]
                 lapply (x2::xs2) elim xs
                  [ *
                    [ normalize in ⊢ (%→?); #H1 destruct (H1) 
                      >Hendci in Hend; #Hend destruct (Hend)
                    | #x3 #xs3 normalize in ⊢ (%→?); #H1 destruct (H1)
                      #_ #Hnotendx3 >(Hnotendx3 ? (memb_hd …)) in Hend;
                      #Hend destruct (Hend)
                    ]
                  | #x3 #xs3 #IHin *
                    [ normalize in ⊢ (%→?); #Hxs3 destruct (Hxs3) #_ #_
                      %{xs3} %
                    | #x4 #xs4 normalize in ⊢ (%→?); #Hxs3xs4 #Hnotend
                      #Hnotendxs4 destruct (Hxs3xs4) cases (IHin ? e0 ??)
                      [ #l0 #Hxs3 >Hxs3 %{l0} %
                      | #c0 #Hc0 @Hnotend cases (orb_true_l … Hc0) -Hc0 #Hc0
                        [ >(\P Hc0) @memb_hd
                        | @memb_cons @memb_cons @Hc0 ]
                      | #c0 #Hc0 @Hnotendxs4 @memb_cons //
                      ]
                    ]
                  ]
                ] * #l2 #Hxs'
                >Hxs' #l3 normalize >associative_append normalize % #H
                destruct (H) lapply (append_l2_injective ?????? e1) //
                #H1 destruct (H1) cases (Hcomp ?? (refl ??)) /2/
              | >Htb >nth_change_vec // >Hmid_dst >Hrs0 % ]
            ]
          ]
        ]
      ]
    |lapply (\Pf eqx) -eqx #eqx >Hmid_dst #Htrue 
     cases (Htrue ? (refl ??) eqx) -Htrue #Htb #Hendcx #_
     cases rs0 in Htb;
     [ #_ %2 #l #l1 cases l
       [ normalize cases xs
         [ cases l1
           [ normalize % #H destruct (H) cases eqx /2/
           | #tmp1 #l2 normalize % #H destruct (H) ]
         | #tmp1 #l2 normalize % #H destruct (H) ]
       | #tmp1 #l2 normalize % #H destruct (H)cases l2 in e0;
         [ normalize #H1 destruct (H1)
         | #tmp2 #l3 normalize #H1 destruct (H1) ]
       ]
     | #r1 #rs1 normalize in ⊢ (???(????%?)→?); #Htb >Htb in IH; #IH
       cases (IH ls x xs end rs ? Hnotend Hend Hnotstart) 
       [| >Htb >nth_change_vec_neq [|@sym_not_eq //] @Hmid_src ] -IH
       #_ #IH cases (IH Hstart (c::ls0) r1 rs1 ?)
       [|| >nth_change_vec // ] -IH
       [ * #l * #l1 * #Hll1 #Hout % %{(c::l)} %{l1} % >Hll1 //
         >reverse_cons >associative_append #cj0 #ls #Hl1 >(Hout ?? Hl1)
         >change_vec_commute in ⊢ (??(???%??)?); // @sym_not_eq //
       | #IH %2 @(not_sub_list_merge_2 ?? (x::xs)) normalize [|@IH]
         #l1 % #H destruct (H) cases eqx /2/
       ] 
    ]
  ]
]
qed.

